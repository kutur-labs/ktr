const std = @import("std");
const ir = @import("ir.zig");
const Ir = ir.Ir;
const Inst = ir.Inst;
const Value = ir.Value;
const Type = ir.Type;
const Operand = ir.Operand;
const Input = ir.Input;

/// Write a numeric value with optional unit suffix.
fn writeValue(writer: anytype, value: Value) !void {
    try value.writeNumber(writer);
    if (value.unit) |u| {
        try writer.writeAll(u.toStr());
    }
}

/// Write an operand (ref or literal).
fn writeOperand(writer: anytype, operand: Operand) !void {
    switch (operand) {
        .ref => |name| try writer.print("%{s}", .{name}),
        .literal => |v| try writeValue(writer, v),
    }
}

/// Serialize an `Ir` to the canonical `.ktrir` text format.
pub fn emit(ir_data: Ir, writer: anytype) !void {
    try writer.print("# ktr-ir v{d}\n", .{ir_data.version});

    if (ir_data.inputs.len > 0 or ir_data.instructions.len > 0) {
        try writer.writeByte('\n');
    }

    for (ir_data.inputs) |input| {
        try writer.print("input %{s} : {s} = ", .{ input.name, input.ty.toStr() });
        try writeValue(writer, input.default);
        try writer.writeByte('\n');
    }

    if (ir_data.inputs.len > 0 and ir_data.instructions.len > 0) {
        try writer.writeByte('\n');
    }

    for (ir_data.instructions) |inst| {
        try writer.print("%{s} : {s} = ", .{ inst.name, inst.ty.toStr() });

        switch (inst.rhs) {
            .constant => |v| try writeValue(writer, v),
            .copy => |name| try writer.print("%{s}", .{name}),
            .builtin => |b| {
                try writer.writeAll(b.op.toStr());
                for (b.operands) |operand| {
                    try writer.writeByte(' ');
                    try writeOperand(writer, operand);
                }
            },
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
    var buf: std.ArrayListUnmanaged(u8) = .{};
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

/// Source -> parse -> sema -> lower -> emit -> parse back, then assert the
/// lowered and re-parsed Ir are structurally identical.
fn expectEmitRoundtrip(source: [:0]const u8) !void {
    const allocator = std.testing.allocator;

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try sema.analyze(allocator, &tree);
    defer sem.deinit();

    var lowered = try lower.lower(allocator, &tree, &sem);
    defer lowered.deinit();

    const text = try emitToString(allocator, lowered);
    defer allocator.free(text);

    var parsed = try ir_parse.parse(allocator, text);
    defer parsed.deinit();

    try std.testing.expect(lowered.eql(parsed));
}

test "roundtrip: lower then emit then parse" {
    try expectEmitRoundtrip("let a = 100mm let b = 50% let c = 42 let d = a");
}

test "emit: builtin op" {
    const allocator = std.testing.allocator;

    var arena = std.heap.ArenaAllocator.init(allocator);
    const ally = arena.allocator();

    const insts = try ally.alloc(Inst, 1);
    insts[0] = .{
        .name = try ally.dupe(u8, "x"),
        .ty = .f64,
        .rhs = .{ .builtin = .{
            .op = .mul,
            .operands = try ally.dupe(Operand, &.{
                Operand{ .ref = try ally.dupe(u8, "a") },
                Operand{ .literal = .{ .number = 2.0, .unit = null } },
            }),
        } },
    };

    var ir_data = Ir{ .instructions = insts, .arena = arena };
    defer ir_data.deinit();

    const output = try emitToString(allocator, ir_data);
    defer allocator.free(output);

    try std.testing.expectEqualStrings(
        \\# ktr-ir v1
        \\
        \\%x : f64 = mul %a 2
        \\
    , output);
}

test "roundtrip: arithmetic emit then parse" {
    try expectEmitRoundtrip("let a = 100mm let x = a * 2");
}

test "roundtrip: complex expression emit then parse" {
    try expectEmitRoundtrip("let x = (2 + 2) / 2");
}

test "emit: input declaration" {
    const allocator = std.testing.allocator;
    var arena = std.heap.ArenaAllocator.init(allocator);
    const ally = arena.allocator();

    const inputs = try ally.alloc(ir.Input, 1);
    inputs[0] = .{
        .name = try ally.dupe(u8, "head"),
        .ty = .length,
        .default = .{ .number = 100.0, .unit = .mm },
    };

    var ir_data = Ir{ .inputs = inputs, .instructions = &.{}, .arena = arena };
    defer ir_data.deinit();

    const output = try emitToString(allocator, ir_data);
    defer allocator.free(output);

    try std.testing.expectEqualStrings(
        \\# ktr-ir v1
        \\
        \\input %head : length = 100mm
        \\
    , output);
}

test "emit: input and instructions separated by blank line" {
    const allocator = std.testing.allocator;
    var arena = std.heap.ArenaAllocator.init(allocator);
    const ally = arena.allocator();

    const inputs = try ally.alloc(ir.Input, 1);
    inputs[0] = .{
        .name = try ally.dupe(u8, "head"),
        .ty = .length,
        .default = .{ .number = 100.0, .unit = .mm },
    };

    const insts = try ally.alloc(Inst, 1);
    insts[0] = .{
        .name = try ally.dupe(u8, "x"),
        .ty = .length,
        .rhs = .{ .copy = try ally.dupe(u8, "head") },
    };

    var ir_data = Ir{ .inputs = inputs, .instructions = insts, .arena = arena };
    defer ir_data.deinit();

    const output = try emitToString(allocator, ir_data);
    defer allocator.free(output);

    try std.testing.expectEqualStrings(
        \\# ktr-ir v1
        \\
        \\input %head : length = 100mm
        \\
        \\%x : length = %head
        \\
    , output);
}

test "roundtrip: input emit then parse" {
    try expectEmitRoundtrip("input head = 100mm let x = head * 2");
}

test "emit: point builtin" {
    const allocator = std.testing.allocator;
    var arena = std.heap.ArenaAllocator.init(allocator);
    const ally = arena.allocator();

    const insts = try ally.alloc(ir.Inst, 1);
    insts[0] = .{
        .name = try ally.dupe(u8, "p"),
        .ty = .point,
        .rhs = .{ .builtin = .{
            .op = .point,
            .operands = try ally.dupe(ir.Operand, &.{
                ir.Operand{ .literal = .{ .number = 100.0, .unit = .mm } },
                ir.Operand{ .literal = .{ .number = 50.0, .unit = .mm } },
            }),
        } },
    };

    var ir_data = ir.Ir{ .instructions = insts, .arena = arena };
    defer ir_data.deinit();

    const output = try emitToString(allocator, ir_data);
    defer allocator.free(output);

    try std.testing.expectEqualStrings(
        \\# ktr-ir v1
        \\
        \\%p : point = point 100mm 50mm
        \\
    , output);
}

test "roundtrip: point emit then parse" {
    try expectEmitRoundtrip("let p = point(100mm, 50mm)");
}

test "roundtrip: point with ref args" {
    try expectEmitRoundtrip("input head = 100mm let p = point(head, 0mm)");
}

test "roundtrip: point with expression args" {
    try expectEmitRoundtrip("input head = 100mm let p = point(head * 2, head / 3)");
}

test "emit: bezier builtin" {
    const allocator = std.testing.allocator;
    var arena = std.heap.ArenaAllocator.init(allocator);
    const ally = arena.allocator();

    const insts = try ally.alloc(ir.Inst, 5);
    insts[0] = .{ .name = try ally.dupe(u8, "p1"), .ty = .point, .rhs = .{ .builtin = .{
        .op = .point,
        .operands = try ally.dupe(ir.Operand, &.{
            ir.Operand{ .literal = .{ .number = 0.0, .unit = .mm } },
            ir.Operand{ .literal = .{ .number = 0.0, .unit = .mm } },
        }),
    } } };
    insts[1] = .{ .name = try ally.dupe(u8, "p2"), .ty = .point, .rhs = .{ .builtin = .{
        .op = .point,
        .operands = try ally.dupe(ir.Operand, &.{
            ir.Operand{ .literal = .{ .number = 100.0, .unit = .mm } },
            ir.Operand{ .literal = .{ .number = 0.0, .unit = .mm } },
        }),
    } } };
    insts[2] = .{ .name = try ally.dupe(u8, "p3"), .ty = .point, .rhs = .{ .builtin = .{
        .op = .point,
        .operands = try ally.dupe(ir.Operand, &.{
            ir.Operand{ .literal = .{ .number = 100.0, .unit = .mm } },
            ir.Operand{ .literal = .{ .number = 100.0, .unit = .mm } },
        }),
    } } };
    insts[3] = .{ .name = try ally.dupe(u8, "p4"), .ty = .point, .rhs = .{ .builtin = .{
        .op = .point,
        .operands = try ally.dupe(ir.Operand, &.{
            ir.Operand{ .literal = .{ .number = 0.0, .unit = .mm } },
            ir.Operand{ .literal = .{ .number = 100.0, .unit = .mm } },
        }),
    } } };
    insts[4] = .{ .name = try ally.dupe(u8, "c"), .ty = .bezier, .rhs = .{ .builtin = .{
        .op = .bezier,
        .operands = try ally.dupe(ir.Operand, &.{
            ir.Operand{ .ref = try ally.dupe(u8, "p1") },
            ir.Operand{ .ref = try ally.dupe(u8, "p2") },
            ir.Operand{ .ref = try ally.dupe(u8, "p3") },
            ir.Operand{ .ref = try ally.dupe(u8, "p4") },
        }),
    } } };

    var ir_data = ir.Ir{ .instructions = insts, .arena = arena };
    defer ir_data.deinit();

    const output = try emitToString(allocator, ir_data);
    defer allocator.free(output);

    try std.testing.expectEqualStrings(
        \\# ktr-ir v1
        \\
        \\%p1 : point = point 0mm 0mm
        \\%p2 : point = point 100mm 0mm
        \\%p3 : point = point 100mm 100mm
        \\%p4 : point = point 0mm 100mm
        \\%c : bezier = bezier %p1 %p2 %p3 %p4
        \\
    , output);
}

test "roundtrip: bezier emit then parse" {
    try expectEmitRoundtrip(
        \\let p1 = point(0mm, 0mm)
        \\let p2 = point(100mm, 0mm)
        \\let p3 = point(100mm, 100mm)
        \\let p4 = point(0mm, 100mm)
        \\let c = bezier(p1, p2, p3, p4)
    );
}
