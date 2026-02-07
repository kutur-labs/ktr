const std = @import("std");
const ir = @import("ir.zig");
const Ir = ir.Ir;
const Inst = ir.Inst;
const Value = ir.Value;
const Type = ir.Type;

/// Write a numeric value with optional unit suffix.
fn writeValue(writer: anytype, value: Value) !void {
    try value.writeNumber(writer);
    if (value.unit) |u| {
        try writer.writeAll(u.toStr());
    }
}

/// Serialize an `Ir` to the canonical `.ktrir` text format.
pub fn emit(ir_data: Ir, writer: anytype) !void {
    try writer.print("# ktr-ir v{d}\n", .{ir_data.version});

    if (ir_data.instructions.len > 0) {
        try writer.writeByte('\n');
    }

    for (ir_data.instructions) |inst| {
        try writer.print("%{s} : {s} = ", .{ inst.name, inst.ty.toStr() });

        switch (inst.rhs) {
            .constant => |v| try writeValue(writer, v),
            .copy => |name| try writer.print("%{s}", .{name}),
        }
        try writer.writeByte('\n');
    }
}

// --- Tests ---

const ir_parse = @import("ir_parse.zig");
const lower = @import("lower.zig");
const parser = @import("parser.zig");
const sema = @import("sema.zig");

fn emitToString(allocator: std.mem.Allocator, ir_data: Ir) ![]const u8 {
    var buf = std.ArrayList(u8).empty;
    errdefer buf.deinit(allocator);
    try emit(ir_data, buf.writer(allocator));
    return buf.toOwnedSlice(allocator);
}

test "emit: empty program" {
    const allocator = std.testing.allocator;
    const arena = std.heap.ArenaAllocator.init(allocator);
    var ir_data = Ir{
        .instructions = &.{},
        .arena = arena,
    };
    defer ir_data.deinit();

    const output = try emitToString(allocator, ir_data);
    defer allocator.free(output);

    try std.testing.expectEqualStrings("# ktr-ir v1\n", output);
}

test "emit: single dimension literal" {
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

    const output = try emitToString(allocator, ir_data);
    defer allocator.free(output);

    try std.testing.expectEqualStrings(
        \\# ktr-ir v1
        \\
        \\%x : length = 100mm
        \\
    , output);
}

test "emit: mixed types" {
    const allocator = std.testing.allocator;
    var arena = std.heap.ArenaAllocator.init(allocator);
    const ally = arena.allocator();

    const insts = try ally.alloc(Inst, 4);
    insts[0] = .{
        .name = try ally.dupe(u8, "x"),
        .ty = .length,
        .rhs = .{ .constant = .{ .number = 100.0, .unit = .mm } },
    };
    insts[1] = .{
        .name = try ally.dupe(u8, "p"),
        .ty = .percentage,
        .rhs = .{ .constant = .{ .number = 50.0, .unit = null } },
    };
    insts[2] = .{
        .name = try ally.dupe(u8, "n"),
        .ty = .f64,
        .rhs = .{ .constant = .{ .number = 42.0, .unit = null } },
    };
    insts[3] = .{
        .name = try ally.dupe(u8, "y"),
        .ty = .length,
        .rhs = .{ .copy = try ally.dupe(u8, "x") },
    };

    var ir_data = Ir{ .instructions = insts, .arena = arena };
    defer ir_data.deinit();

    const output = try emitToString(allocator, ir_data);
    defer allocator.free(output);

    try std.testing.expectEqualStrings(
        \\# ktr-ir v1
        \\
        \\%x : length = 100mm
        \\%p : percentage = 50
        \\%n : f64 = 42
        \\%y : length = %x
        \\
    , output);
}

test "roundtrip: emit then parse produces identical Ir" {
    const allocator = std.testing.allocator;

    // Build an Ir by hand.
    var arena = std.heap.ArenaAllocator.init(allocator);
    const ally = arena.allocator();

    const insts = try ally.alloc(Inst, 4);
    insts[0] = .{
        .name = try ally.dupe(u8, "x"),
        .ty = .length,
        .rhs = .{ .constant = .{ .number = 100.0, .unit = .mm } },
    };
    insts[1] = .{
        .name = try ally.dupe(u8, "p"),
        .ty = .percentage,
        .rhs = .{ .constant = .{ .number = 50.0, .unit = null } },
    };
    insts[2] = .{
        .name = try ally.dupe(u8, "n"),
        .ty = .f64,
        .rhs = .{ .constant = .{ .number = 42.0, .unit = null } },
    };
    insts[3] = .{
        .name = try ally.dupe(u8, "y"),
        .ty = .length,
        .rhs = .{ .copy = try ally.dupe(u8, "x") },
    };

    var original = Ir{ .instructions = insts, .arena = arena };
    defer original.deinit();

    // Emit to text.
    const text = try emitToString(allocator, original);
    defer allocator.free(text);

    // Parse back.
    var parsed = try ir_parse.parse(allocator, text);
    defer parsed.deinit();

    // Compare.
    try std.testing.expect(original.eql(parsed));
}

test "roundtrip: lower then emit then parse" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "let a = 100mm let b = 50% let c = 42 let d = a";

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try sema.analyze(allocator, &tree);
    defer sem.deinit();

    var lowered = try lower.lower(allocator, &tree, &sem);
    defer lowered.deinit();

    // Emit to text.
    const text = try emitToString(allocator, lowered);
    defer allocator.free(text);

    // Parse back.
    var parsed = try ir_parse.parse(allocator, text);
    defer parsed.deinit();

    // Lowered and parsed Ir should be structurally equal.
    try std.testing.expect(lowered.eql(parsed));
}
