const std = @import("std");
const ir = @import("ir.zig");
const Ir = ir.Ir;
const Inst = ir.Inst;
const Value = ir.Value;
const Type = ir.Type;

/// Write a numeric literal in ktr source form.
///
/// Length values include the unit suffix (`100mm`). Percentage values include
/// the `%` suffix (`50%`). Bare f64 values are emitted without suffix (`42`).
fn writeKtrValue(writer: anytype, value: Value, ty: Type) !void {
    try value.writeNumber(writer);
    if (value.unit) |u| {
        try writer.writeAll(u.toStr());
    } else if (ty == .percentage) {
        try writer.writeByte('%');
    }
}

/// Reconstruct `.ktr` source from an `Ir`.
///
/// For the current subset (let bindings with constants and copies), each
/// instruction maps directly to a `let` statement.
pub fn decompile(ir_data: Ir, writer: anytype) !void {
    for (ir_data.instructions, 0..) |inst, i| {
        if (i > 0) try writer.writeByte('\n');

        try writer.print("let {s} = ", .{inst.name});

        switch (inst.rhs) {
            .constant => |v| try writeKtrValue(writer, v, inst.ty),
            .copy => |name| try writer.writeAll(name),
        }
    }

    // Trailing newline if there was any output.
    if (ir_data.instructions.len > 0) {
        try writer.writeByte('\n');
    }
}

// --- Tests ---

const parser = @import("parser.zig");
const sema = @import("sema.zig");
const lower = @import("lower.zig");

fn decompileToString(allocator: std.mem.Allocator, ir_data: Ir) ![]const u8 {
    var buf = std.ArrayList(u8).empty;
    errdefer buf.deinit(allocator);
    try decompile(ir_data, buf.writer(allocator));
    return buf.toOwnedSlice(allocator);
}

test "decompile: single dimension literal" {
    const allocator = std.testing.allocator;
    var arena = std.heap.ArenaAllocator.init(allocator);
    const ally = arena.allocator();

    const insts = try ally.alloc(Inst, 1);
    insts[0] = .{
        .name = try ally.dupe(u8, "x"),
        .ty = .length,
        .rhs = .{ .constant = .{ .number = 100.0, .unit = .mm } },
    };

    var ir_data = Ir{ .instructions = insts, .arena = arena };
    defer ir_data.deinit();

    const output = try decompileToString(allocator, ir_data);
    defer allocator.free(output);

    try std.testing.expectEqualStrings("let x = 100mm\n", output);
}

test "decompile: percentage literal" {
    const allocator = std.testing.allocator;
    var arena = std.heap.ArenaAllocator.init(allocator);
    const ally = arena.allocator();

    const insts = try ally.alloc(Inst, 1);
    insts[0] = .{
        .name = try ally.dupe(u8, "p"),
        .ty = .percentage,
        .rhs = .{ .constant = .{ .number = 50.0, .unit = null } },
    };

    var ir_data = Ir{ .instructions = insts, .arena = arena };
    defer ir_data.deinit();

    const output = try decompileToString(allocator, ir_data);
    defer allocator.free(output);

    try std.testing.expectEqualStrings("let p = 50%\n", output);
}

test "decompile: bare number" {
    const allocator = std.testing.allocator;
    var arena = std.heap.ArenaAllocator.init(allocator);
    const ally = arena.allocator();

    const insts = try ally.alloc(Inst, 1);
    insts[0] = .{
        .name = try ally.dupe(u8, "n"),
        .ty = .f64,
        .rhs = .{ .constant = .{ .number = 42.0, .unit = null } },
    };

    var ir_data = Ir{ .instructions = insts, .arena = arena };
    defer ir_data.deinit();

    const output = try decompileToString(allocator, ir_data);
    defer allocator.free(output);

    try std.testing.expectEqualStrings("let n = 42\n", output);
}

test "decompile: copy reference" {
    const allocator = std.testing.allocator;
    var arena = std.heap.ArenaAllocator.init(allocator);
    const ally = arena.allocator();

    const insts = try ally.alloc(Inst, 2);
    insts[0] = .{
        .name = try ally.dupe(u8, "x"),
        .ty = .length,
        .rhs = .{ .constant = .{ .number = 100.0, .unit = .mm } },
    };
    insts[1] = .{
        .name = try ally.dupe(u8, "y"),
        .ty = .length,
        .rhs = .{ .copy = try ally.dupe(u8, "x") },
    };

    var ir_data = Ir{ .instructions = insts, .arena = arena };
    defer ir_data.deinit();

    const output = try decompileToString(allocator, ir_data);
    defer allocator.free(output);

    try std.testing.expectEqualStrings("let x = 100mm\nlet y = x\n", output);
}

test "decompile: empty program" {
    const allocator = std.testing.allocator;
    const arena = std.heap.ArenaAllocator.init(allocator);
    var ir_data = Ir{
        .instructions = &.{},
        .arena = arena,
    };
    defer ir_data.deinit();

    const output = try decompileToString(allocator, ir_data);
    defer allocator.free(output);

    try std.testing.expectEqualStrings("", output);
}

test "decompile: mixed types" {
    const allocator = std.testing.allocator;
    var arena = std.heap.ArenaAllocator.init(allocator);
    const ally = arena.allocator();

    const insts = try ally.alloc(Inst, 3);
    insts[0] = .{
        .name = try ally.dupe(u8, "a"),
        .ty = .length,
        .rhs = .{ .constant = .{ .number = 100.0, .unit = .mm } },
    };
    insts[1] = .{
        .name = try ally.dupe(u8, "b"),
        .ty = .percentage,
        .rhs = .{ .constant = .{ .number = 50.0, .unit = null } },
    };
    insts[2] = .{
        .name = try ally.dupe(u8, "c"),
        .ty = .f64,
        .rhs = .{ .constant = .{ .number = 42.0, .unit = null } },
    };

    var ir_data = Ir{ .instructions = insts, .arena = arena };
    defer ir_data.deinit();

    const output = try decompileToString(allocator, ir_data);
    defer allocator.free(output);

    const expected =
        \\let a = 100mm
        \\let b = 50%
        \\let c = 42
        \\
    ;
    try std.testing.expectEqualStrings(expected, output);
}

test "decompile roundtrip: source -> lower -> decompile -> re-lower -> compare" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "let a = 100mm\nlet b = 50%\nlet c = 42\nlet d = a";

    // First pass: parse -> sema -> lower.
    var tree1 = try parser.parse(allocator, source);
    defer tree1.deinit();

    var sem1 = try sema.analyze(allocator, &tree1);
    defer sem1.deinit();

    var ir1 = try lower.lower(allocator, &tree1, &sem1);
    defer ir1.deinit();

    // Decompile back to .ktr source.
    var buf = std.ArrayList(u8).empty;
    defer buf.deinit(allocator);
    try decompile(ir1, buf.writer(allocator));
    const ktr_text = try buf.toOwnedSlice(allocator);
    defer allocator.free(ktr_text);

    // Second pass: re-parse the decompiled source -> sema -> lower.
    const ktr_z = try allocator.dupeZ(u8, ktr_text);
    defer allocator.free(ktr_z);

    var tree2 = try parser.parse(allocator, ktr_z);
    defer tree2.deinit();

    var sem2 = try sema.analyze(allocator, &tree2);
    defer sem2.deinit();

    try std.testing.expect(!sem2.hasErrors());

    var ir2 = try lower.lower(allocator, &tree2, &sem2);
    defer ir2.deinit();

    // The two Ir representations should be structurally identical.
    try std.testing.expect(ir1.eql(ir2));
}
