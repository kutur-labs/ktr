const std = @import("std");
const ast = @import("ast.zig");
const parser = @import("parser.zig");
const sema = @import("sema.zig");
const lower_mod = @import("lower.zig");
const ir_emit = @import("ir_emit.zig");
const ir_parse = @import("ir_parse.zig");
const ir_decompile = @import("ir_decompile.zig");

const allocator = std.heap.wasm_allocator;

// ─── Global result buffers ──────────────────────────────────────────────────

var output_buf: ?[]u8 = null;
var error_buf: ?[]u8 = null;

fn freeOutput() void {
    if (output_buf) |buf| allocator.free(buf);
    output_buf = null;
}

fn freeError() void {
    if (error_buf) |buf| allocator.free(buf);
    error_buf = null;
}

// ─── Diagnostics ────────────────────────────────────────────────────────────

fn formatDiagnostics(
    source: []const u8,
    tokens: ast.TokenList,
    diagnostics: []const ast.Diagnostic,
) void {
    freeError();
    var buf = std.ArrayList(u8).empty;
    const writer = buf.writer(allocator);
    for (diagnostics, 0..) |diag, i| {
        if (i > 0) writer.writeByte('\n') catch return;
        const start = tokens.items(.start)[diag.token];
        const end = tokens.items(.end)[diag.token];
        const loc = ast.computeLineCol(source, start);
        const token_len = end - start;
        writer.print("{d}:{d}:{d}: error: {s}", .{
            loc[0], loc[1], token_len, diag.tag.message(),
        }) catch return;
    }
    error_buf = buf.toOwnedSlice(allocator) catch null;
}

// ─── Exported WASM API ──────────────────────────────────────────────────────

/// Allocate `len` bytes of WASM memory. Returns a pointer for JS to write into.
export fn alloc(len: usize) usize {
    const slice = allocator.alloc(u8, len) catch return 0;
    return @intFromPtr(slice.ptr);
}

/// Free a previously allocated region.
export fn dealloc(ptr: usize, len: usize) void {
    if (ptr == 0) return;
    const slice: [*]u8 = @ptrFromInt(ptr);
    allocator.free(slice[0..len]);
}

/// Compile `.ktr` source to `.ktrir` text.
///
/// Returns the output length on success (>= 0), or a negative error code:
///   -1  out of memory / internal error
///   -2  parse error   (check get_error_ptr / get_error_len)
///   -3  semantic error (check get_error_ptr / get_error_len)
export fn compile(input_ptr: usize, input_len: usize) i32 {
    freeOutput();
    freeError();

    if (input_ptr == 0) return -1;
    const raw: [*]const u8 = @ptrFromInt(input_ptr);
    const source_raw = raw[0..input_len];

    // Null-terminate for the parser.
    const source: [:0]const u8 = allocator.dupeZ(u8, source_raw) catch return -1;
    defer allocator.free(source);

    // Parse.
    var tree = parser.parse(allocator, source) catch return -1;
    defer tree.deinit();

    if (tree.hasErrors()) {
        formatDiagnostics(source, tree.tokens, tree.diagnostics);
        return -2;
    }

    // Semantic analysis.
    var sem = sema.analyze(allocator, &tree) catch return -1;
    defer sem.deinit();

    if (sem.hasErrors()) {
        formatDiagnostics(source, tree.tokens, sem.diagnostics);
        return -3;
    }

    // Lower to IR.
    var ir_data = lower_mod.lower(allocator, &tree, &sem) catch return -1;
    defer ir_data.deinit();

    // Emit IR text.
    var buf = std.ArrayList(u8).empty;
    ir_emit.emit(ir_data, buf.writer(allocator)) catch return -1;
    output_buf = buf.toOwnedSlice(allocator) catch return -1;

    return @intCast(output_buf.?.len);
}

/// Decompile `.ktrir` text back to `.ktr` source.
///
/// Returns the output length on success (>= 0), or a negative error code:
///   -1  out of memory / internal error
///   -2  invalid IR format (check get_error_ptr / get_error_len)
export fn decompile_ir(input_ptr: usize, input_len: usize) i32 {
    freeOutput();
    freeError();

    if (input_ptr == 0) return -1;
    const raw: [*]const u8 = @ptrFromInt(input_ptr);
    const source = raw[0..input_len];

    // Parse IR.
    var ir_data = ir_parse.parse(allocator, source) catch {
        const msg = "invalid .ktrir input";
        error_buf = allocator.dupe(u8, msg) catch null;
        return -2;
    };
    defer ir_data.deinit();

    // Decompile to .ktr source.
    var buf = std.ArrayList(u8).empty;
    ir_decompile.decompile(allocator, ir_data, buf.writer(allocator)) catch return -1;
    output_buf = buf.toOwnedSlice(allocator) catch return -1;

    return @intCast(output_buf.?.len);
}

/// Pointer to the last successful output buffer.
export fn get_output_ptr() usize {
    if (output_buf) |buf| return @intFromPtr(buf.ptr);
    return 0;
}

/// Length of the last successful output buffer.
export fn get_output_len() usize {
    if (output_buf) |buf| return buf.len;
    return 0;
}

/// Pointer to the last error message buffer.
export fn get_error_ptr() usize {
    if (error_buf) |buf| return @intFromPtr(buf.ptr);
    return 0;
}

/// Length of the last error message buffer.
export fn get_error_len() usize {
    if (error_buf) |buf| return buf.len;
    return 0;
}
