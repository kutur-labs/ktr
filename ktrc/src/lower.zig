const std = @import("std");
const ast = @import("ast.zig");
const Ast = ast.Ast;
const sema = @import("sema.zig");
const Sema = sema.Sema;
const ir = @import("ir.zig");
const Ir = ir.Ir;
const Inst = ir.Inst;
const Value = ir.Value;
const LengthUnit = ir.LengthUnit;
const Type = ir.Type;

/// Map a sema type to an IR type. Poison must never reach this point.
fn mapType(sema_ty: sema.Type) Type {
    return switch (sema_ty) {
        .length => .length,
        .percentage => .percentage,
        .number => .f64,
        .poison => unreachable,
    };
}

/// Lower a semantically-analyzed AST into the intermediate representation.
///
/// Precondition: `sema` must have no errors (`!sema.hasErrors()`).
/// The returned `Ir` owns all its memory via an arena; call `Ir.deinit()`
/// when done.
pub fn lower(gpa: std.mem.Allocator, tree: *const Ast, sema_result: *const Sema) (std.mem.Allocator.Error || error{InvalidLiteral})!Ir {
    std.debug.assert(!sema_result.hasErrors());

    var arena = std.heap.ArenaAllocator.init(gpa);
    errdefer arena.deinit();
    const ally = arena.allocator();

    const count = sema_result.symbols.count();
    const instructions = try ally.alloc(Inst, count);

    const keys = sema_result.symbols.keys();
    const values = sema_result.symbols.values();

    for (keys, values, 0..) |name, sym, i| {
        const node = tree.nodes.get(sym.node);
        // node is a let_statement; the value expression is at data.lhs.
        const value_node = tree.nodes.get(node.data.lhs);

        const duped_name = try ally.dupe(u8, name);
        const ty = mapType(sym.ty);

        const text = tree.tokenSlice(value_node.main_token);
        const rhs: Inst.Rhs = switch (value_node.tag) {
            .dimension_literal, .number_literal => .{
                .constant = Value.parse(text) catch return error.InvalidLiteral,
            },
            .percentage_literal => .{
                .constant = Value.parse(text[0 .. text.len - 1]) catch return error.InvalidLiteral,
            },
            .identifier_ref => .{
                .copy = try ally.dupe(u8, tree.tokenSlice(value_node.main_token)),
            },
            // Only expression nodes appear as let values.
            .root, .let_statement => unreachable,
        };

        instructions[i] = .{
            .name = duped_name,
            .ty = ty,
            .rhs = rhs,
        };
    }

    return .{
        .version = 1,
        .instructions = instructions,
        .arena = arena,
    };
}

// --- Tests ---

const parser = @import("parser.zig");

fn lowerSource(allocator: std.mem.Allocator, source: [:0]const u8) !Ir {
    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try sema.analyze(allocator, &tree);
    defer sem.deinit();

    std.debug.assert(!sem.hasErrors());
    return lower(allocator, &tree, &sem);
}

test "lower: let x = 100mm" {
    const allocator = std.testing.allocator;
    var result = try lowerSource(allocator, "let x = 100mm");
    defer result.deinit();

    try std.testing.expectEqual(1, result.instructions.len);
    const inst = result.instructions[0];

    try std.testing.expectEqualStrings("x", inst.name);
    try std.testing.expectEqual(Type.length, inst.ty);

    switch (inst.rhs) {
        .constant => |v| {
            try std.testing.expectEqual(@as(f64, 100.0), v.number);
            try std.testing.expectEqual(LengthUnit.mm, v.unit.?);
        },
        .copy => return error.TestUnexpectedResult,
    }
}

test "lower: let p = 50%" {
    const allocator = std.testing.allocator;
    var result = try lowerSource(allocator, "let p = 50%");
    defer result.deinit();

    try std.testing.expectEqual(1, result.instructions.len);
    const inst = result.instructions[0];

    try std.testing.expectEqualStrings("p", inst.name);
    try std.testing.expectEqual(Type.percentage, inst.ty);

    switch (inst.rhs) {
        .constant => |v| {
            try std.testing.expectEqual(@as(f64, 50.0), v.number);
            try std.testing.expectEqual(@as(?LengthUnit, null), v.unit);
        },
        .copy => return error.TestUnexpectedResult,
    }
}

test "lower: let n = 42" {
    const allocator = std.testing.allocator;
    var result = try lowerSource(allocator, "let n = 42");
    defer result.deinit();

    try std.testing.expectEqual(1, result.instructions.len);
    const inst = result.instructions[0];

    try std.testing.expectEqualStrings("n", inst.name);
    try std.testing.expectEqual(Type.f64, inst.ty);

    switch (inst.rhs) {
        .constant => |v| {
            try std.testing.expectEqual(@as(f64, 42.0), v.number);
            try std.testing.expectEqual(@as(?LengthUnit, null), v.unit);
        },
        .copy => return error.TestUnexpectedResult,
    }
}

test "lower: let y = x (copy)" {
    const allocator = std.testing.allocator;
    var result = try lowerSource(allocator, "let x = 100mm let y = x");
    defer result.deinit();

    try std.testing.expectEqual(2, result.instructions.len);

    // First instruction: %x : length = 100mm
    const inst_x = result.instructions[0];
    try std.testing.expectEqualStrings("x", inst_x.name);
    try std.testing.expectEqual(Type.length, inst_x.ty);

    // Second instruction: %y : length = %x
    const inst_y = result.instructions[1];
    try std.testing.expectEqualStrings("y", inst_y.name);
    try std.testing.expectEqual(Type.length, inst_y.ty);

    switch (inst_y.rhs) {
        .copy => |name| try std.testing.expectEqualStrings("x", name),
        .constant => return error.TestUnexpectedResult,
    }
}

test "lower: multiple bindings with mixed types" {
    const allocator = std.testing.allocator;
    var result = try lowerSource(allocator, "let a = 100mm let b = 50% let c = 42");
    defer result.deinit();

    try std.testing.expectEqual(3, result.instructions.len);

    try std.testing.expectEqualStrings("a", result.instructions[0].name);
    try std.testing.expectEqual(Type.length, result.instructions[0].ty);

    try std.testing.expectEqualStrings("b", result.instructions[1].name);
    try std.testing.expectEqual(Type.percentage, result.instructions[1].ty);

    try std.testing.expectEqualStrings("c", result.instructions[2].name);
    try std.testing.expectEqual(Type.f64, result.instructions[2].ty);
}

test "lower: dimension with cm unit" {
    const allocator = std.testing.allocator;
    var result = try lowerSource(allocator, "let w = 25cm");
    defer result.deinit();

    const inst = result.instructions[0];
    switch (inst.rhs) {
        .constant => |v| {
            try std.testing.expectEqual(@as(f64, 25.0), v.number);
            try std.testing.expectEqual(LengthUnit.cm, v.unit.?);
        },
        .copy => return error.TestUnexpectedResult,
    }
}

