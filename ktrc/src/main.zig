const std = @import("std");
const Allocator = std.mem.Allocator;

const ast = @import("ast.zig");
const parser = @import("parser.zig");
const sema = @import("sema.zig");
const lower = @import("lower.zig");
const ir_emit = @import("ir_emit.zig");
const ir_parse = @import("ir_parse.zig");
const ir_decompile = @import("ir_decompile.zig");

/// Maximum source/IR size accepted (10 MiB).
const max_source_bytes = 10 * 1024 * 1024;

// ─── Diagnostics ────────────────────────────────────────────────────────────

fn fatal(comptime fmt: []const u8, args: anytype) noreturn {
    const msg = std.fmt.allocPrint(std.heap.page_allocator, "ktrc: error: " ++ fmt ++ "\n", args) catch @panic("OOM");
    std.fs.File.stderr().writeAll(msg) catch {};
    std.process.exit(1);
}

fn usageError(comptime fmt: []const u8, args: anytype) noreturn {
    const msg = std.fmt.allocPrint(std.heap.page_allocator, "ktrc: " ++ fmt ++ "\n", args) catch @panic("OOM");
    const stderr = std.fs.File.stderr();
    stderr.writeAll(msg) catch {};
    stderr.writeAll("Run 'ktrc help' for usage information.\n") catch {};
    std.process.exit(2);
}

fn reportDiagnostics(
    source: []const u8,
    tokens: ast.TokenList,
    diagnostics: []const ast.Diagnostic,
    file_name: []const u8,
) void {
    const stderr = std.fs.File.stderr();
    for (diagnostics) |diag| {
        const start = tokens.items(.start)[diag.token];
        const loc = ast.computeLineCol(source, start);
        const msg = std.fmt.allocPrint(std.heap.page_allocator, "{s}:{d}:{d}: error: {s}\n", .{
            file_name, loc[0], loc[1], diag.tag.message(),
        }) catch continue;
        stderr.writeAll(msg) catch {};
    }
}

// ─── I/O ────────────────────────────────────────────────────────────────────

/// Read raw bytes from a file path, or from stdin when path is null.
fn readInput(gpa: Allocator, path: ?[]const u8) []const u8 {
    if (path) |p| {
        return std.fs.cwd().readFileAlloc(gpa, p, max_source_bytes) catch |err| {
            fatal("cannot read '{s}': {s}", .{ p, @errorName(err) });
        };
    }
    // Read from stdin in chunks.
    var list = std.ArrayList(u8).empty;
    const stdin = std.fs.File.stdin();
    while (true) {
        var buf: [4096]u8 = undefined;
        const n = stdin.read(&buf) catch |err| {
            fatal("cannot read stdin: {s}", .{@errorName(err)});
        };
        if (n == 0) break;
        list.appendSlice(gpa, buf[0..n]) catch fatal("out of memory", .{});
    }
    return list.toOwnedSlice(gpa) catch fatal("out of memory", .{});
}

/// Write output bytes to a file path, or to stdout when path is null.
fn writeOutput(path: ?[]const u8, content: []const u8) void {
    if (path) |p| {
        const file = std.fs.cwd().createFile(p, .{}) catch |err| {
            fatal("cannot create '{s}': {s}", .{ p, @errorName(err) });
        };
        defer file.close();
        file.writeAll(content) catch |err| {
            fatal("cannot write '{s}': {s}", .{ p, @errorName(err) });
        };
    } else {
        std.fs.File.stdout().writeAll(content) catch |err| {
            fatal("cannot write stdout: {s}", .{@errorName(err)});
        };
    }
}

// ─── Argument Parsing ───────────────────────────────────────────────────────

const CommandArgs = struct {
    input_path: ?[]const u8 = null,
    output_path: ?[]const u8 = null,
};

fn parseCommandArgs(args: []const [:0]const u8) CommandArgs {
    var result: CommandArgs = .{};
    var i: usize = 0;
    while (i < args.len) : (i += 1) {
        const arg: []const u8 = args[i];
        if (std.mem.eql(u8, arg, "-o")) {
            i += 1;
            if (i >= args.len) usageError("option '-o' requires an argument", .{});
            result.output_path = args[i];
        } else if (std.mem.eql(u8, arg, "--help") or std.mem.eql(u8, arg, "-h")) {
            std.fs.File.stdout().writeAll(usage_text) catch {};
            std.process.exit(0);
        } else if (arg.len > 0 and arg[0] == '-') {
            usageError("unknown option '{s}'", .{arg});
        } else {
            if (result.input_path != null) usageError("unexpected argument '{s}'", .{arg});
            result.input_path = arg;
        }
    }
    return result;
}

// ─── Commands ───────────────────────────────────────────────────────────────

fn cmdCompile(gpa: Allocator, args: []const [:0]const u8) void {
    const opts = parseCommandArgs(args);
    const file_name: []const u8 = opts.input_path orelse "<stdin>";

    // Read source.
    const raw = readInput(gpa, opts.input_path);
    const source: [:0]const u8 = gpa.dupeZ(u8, raw) catch fatal("out of memory", .{});
    gpa.free(raw);
    defer gpa.free(source);

    // Parse.
    var tree = parser.parse(gpa, source) catch fatal("out of memory", .{});
    defer tree.deinit();

    if (tree.hasErrors()) {
        reportDiagnostics(source, tree.tokens, tree.diagnostics, file_name);
        std.process.exit(1);
    }

    // Semantic analysis.
    var sem = sema.analyze(gpa, &tree) catch fatal("out of memory", .{});
    defer sem.deinit();

    if (sem.hasErrors()) {
        reportDiagnostics(source, tree.tokens, sem.diagnostics, file_name);
        std.process.exit(1);
    }

    // Lower to IR.
    var ir_data = lower.lower(gpa, &tree, &sem) catch |err| switch (err) {
        error.InvalidLiteral => fatal("invalid literal encountered during lowering", .{}),
        error.OutOfMemory => fatal("out of memory", .{}),
    };
    defer ir_data.deinit();

    // Emit IR text.
    var buf = std.ArrayList(u8).empty;
    defer buf.deinit(gpa);
    ir_emit.emit(ir_data, buf.writer(gpa)) catch fatal("failed to emit IR", .{});
    const output = buf.toOwnedSlice(gpa) catch fatal("out of memory", .{});
    defer gpa.free(output);

    writeOutput(opts.output_path, output);
}

fn cmdDecompile(gpa: Allocator, args: []const [:0]const u8) void {
    const opts = parseCommandArgs(args);

    // Read IR text.
    const raw = readInput(gpa, opts.input_path);
    defer gpa.free(raw);

    // Parse IR.
    var ir_data = ir_parse.parse(gpa, raw) catch |err| {
        fatal("invalid .ktrir input: {s}", .{@errorName(err)});
    };
    defer ir_data.deinit();

    // Decompile to .ktr source.
    var buf = std.ArrayList(u8).empty;
    defer buf.deinit(gpa);
    ir_decompile.decompile(gpa, ir_data, buf.writer(gpa)) catch fatal("failed to decompile", .{});
    const output = buf.toOwnedSlice(gpa) catch fatal("out of memory", .{});
    defer gpa.free(output);

    writeOutput(opts.output_path, output);
}

// ─── Help / Version ─────────────────────────────────────────────────────────

const usage_text =
    \\Usage: ktrc <command> [options] [file]
    \\
    \\Commands:
    \\  compile      Compile .ktr source to .ktrir
    \\  decompile    Decompile .ktrir back to .ktr source
    \\  version      Print version information
    \\  help         Print this help message
    \\
    \\Options:
    \\  -o <file>    Write output to <file> instead of stdout
    \\  -h, --help   Print help
    \\
    \\When no file is given, input is read from stdin.
    \\
    \\Examples:
    \\  ktrc compile program.ktr
    \\  ktrc compile program.ktr -o output.ktrir
    \\  ktrc compile < program.ktr
    \\  ktrc decompile output.ktrir
    \\  cat file.ktr | ktrc compile | ktrc decompile
    \\
;

// ─── Entry Point ────────────────────────────────────────────────────────────

pub fn main() void {
    var gpa_state: std.heap.GeneralPurposeAllocator(.{}) = .{};
    defer _ = gpa_state.deinit();
    const gpa = gpa_state.allocator();

    const args = std.process.argsAlloc(gpa) catch fatal("out of memory", .{});
    defer std.process.argsFree(gpa, args);

    if (args.len < 2) {
        std.fs.File.stderr().writeAll(usage_text) catch {};
        std.process.exit(2);
    }

    const cmd: []const u8 = args[1];
    const cmd_args = args[2..];

    if (std.mem.eql(u8, cmd, "compile")) {
        cmdCompile(gpa, cmd_args);
    } else if (std.mem.eql(u8, cmd, "decompile")) {
        cmdDecompile(gpa, cmd_args);
    } else if (std.mem.eql(u8, cmd, "version") or std.mem.eql(u8, cmd, "--version") or std.mem.eql(u8, cmd, "-v")) {
        std.fs.File.stdout().writeAll("ktrc 0.1.0\n") catch {};
    } else if (std.mem.eql(u8, cmd, "help") or std.mem.eql(u8, cmd, "--help") or std.mem.eql(u8, cmd, "-h")) {
        std.fs.File.stdout().writeAll(usage_text) catch {};
    } else {
        usageError("unknown command '{s}'", .{cmd});
    }
}
