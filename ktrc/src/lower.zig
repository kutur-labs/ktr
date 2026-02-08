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
const Op = ir.Op;
const Operand = ir.Operand;
const Input = ir.Input;

/// Map a sema type to an IR type. Poison must never reach this point.
fn mapType(sema_ty: sema.Type) Type {
    return switch (sema_ty) {
        .length => .length,
        .percentage => .percentage,
        .f64 => .f64,
        .poison => unreachable,
    };
}

const Lowerer = struct {
    tree: *const Ast,
    sema_result: *const Sema,
    ally: std.mem.Allocator,
    inputs: std.ArrayListUnmanaged(Input),
    instructions: std.ArrayListUnmanaged(Inst),
    temp_counter: u32,

    const LowerError = std.mem.Allocator.Error || error{InvalidLiteral};

    /// Generate a temp name like "0", "1", etc.
    fn tempName(self: *Lowerer) LowerError![]const u8 {
        const name = try std.fmt.allocPrint(self.ally, "{d}", .{self.temp_counter});
        self.temp_counter += 1;
        return name;
    }

    /// Map an AST node tag to an IR op.
    fn mapOp(tag: ast.Node.Tag) Op {
        return switch (tag) {
            .add => .add,
            .sub => .sub,
            .mul => .mul,
            .div => .div,
            else => unreachable,
        };
    }

    /// Look up the IR type for an expression node via the sema result.
    fn nodeType(self: *Lowerer, node_index: ast.NodeIndex) Type {
        return mapType(self.sema_result.node_types[node_index]);
    }

    /// Parse an AST literal node (dimension, percentage, or number) into an IR Value.
    fn parseLiteralValue(self: *Lowerer, node_index: ast.NodeIndex) error{InvalidLiteral}!Value {
        const node = self.tree.nodes.get(node_index);
        const text = self.tree.tokenSlice(node.main_token);
        return switch (node.tag) {
            .dimension_literal, .number_literal => Value.parse(text) catch return error.InvalidLiteral,
            .percentage_literal => Value.parse(text[0 .. text.len - 1]) catch return error.InvalidLiteral,
            else => error.InvalidLiteral,
        };
    }

    /// Lower an expression node. For leaf nodes, returns an Operand directly
    /// (no instruction emitted). For binary ops, emits intermediate instructions
    /// with temp names and returns a ref operand to the result.
    fn lowerExpr(self: *Lowerer, node_index: ast.NodeIndex) LowerError!Operand {
        const node = self.tree.nodes.get(node_index);
        return switch (node.tag) {
            .dimension_literal, .number_literal, .percentage_literal => {
                return .{ .literal = try self.parseLiteralValue(node_index) };
            },
            .identifier_ref => {
                return .{ .ref = try self.ally.dupe(u8, self.tree.tokenSlice(node.main_token)) };
            },
            .grouped_expression => {
                return self.lowerExpr(node.data.lhs);
            },
            .add, .sub, .mul, .div => {
                const lhs_operand = try self.lowerExpr(node.data.lhs);
                const rhs_operand = try self.lowerExpr(node.data.rhs);

                const ty = self.nodeType(node_index);
                const name = try self.tempName();

                try self.instructions.append(self.ally, .{
                    .name = name,
                    .ty = ty,
                    .rhs = .{ .builtin = .{
                        .op = mapOp(node.tag),
                        .lhs = lhs_operand,
                        .rhs = rhs_operand,
                    } },
                });

                return .{ .ref = name };
            },
            .root, .let_statement, .input_statement => unreachable,
        };
    }

    /// Lower a let binding. Delegates to `lowerExpr` for all node types,
    /// then converts the resulting operand into a named instruction.
    ///
    /// When the expression is a binary op, `lowerExpr` emits a temp-named
    /// instruction and returns a ref to it. We rename that instruction in
    /// place to avoid an extra copy. The assertion guards this assumption:
    /// if `lowerExpr` changes to emit multiple instructions, it will fire.
    fn lowerLet(self: *Lowerer, name: []const u8, sym: sema.Symbol) LowerError!void {
        const node = self.tree.nodes.get(sym.node);
        const ty = mapType(sym.ty);
        const duped_name = try self.ally.dupe(u8, name);

        const inst_count_before = self.instructions.items.len;
        const operand = try self.lowerExpr(node.data.lhs);
        const emitted_new = self.instructions.items.len > inst_count_before;

        switch (operand) {
            .ref => |ref_name| {
                if (emitted_new) {
                    // Rename the last emitted temp to the user binding name.
                    const last = &self.instructions.items[self.instructions.items.len - 1];
                    std.debug.assert(std.mem.eql(u8, last.name, ref_name));
                    last.name = duped_name;
                } else {
                    // Identifier ref: emit a copy instruction.
                    try self.instructions.append(self.ally, .{
                        .name = duped_name,
                        .ty = ty,
                        .rhs = .{ .copy = ref_name },
                    });
                }
            },
            .literal => |v| {
                try self.instructions.append(self.ally, .{
                    .name = duped_name,
                    .ty = ty,
                    .rhs = .{ .constant = v },
                });
            },
        }
    }

    /// Lower an input declaration. The parser enforces that the default is a
    /// leaf literal; `parseLiteralValue` returns InvalidLiteral for anything else.
    fn lowerInput(self: *Lowerer, name: []const u8, sym: sema.Symbol) LowerError!void {
        const node = self.tree.nodes.get(sym.node);
        const value = try self.parseLiteralValue(node.data.lhs);
        try self.inputs.append(self.ally, .{
            .name = try self.ally.dupe(u8, name),
            .ty = mapType(sym.ty),
            .default = value,
        });
    }
};

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

    var l = Lowerer{
        .tree = tree,
        .sema_result = sema_result,
        .ally = ally,
        .inputs = .{},
        .instructions = .{},
        .temp_counter = 0,
    };

    const keys = sema_result.symbols.keys();
    const values = sema_result.symbols.values();

    for (keys, values) |name, sym| {
        switch (sym.kind) {
            .input => try l.lowerInput(name, sym),
            .let_binding => try l.lowerLet(name, sym),
        }
    }

    return .{
        .version = 1,
        .inputs = try l.inputs.toOwnedSlice(ally),
        .instructions = try l.instructions.toOwnedSlice(ally),
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
        else => return error.TestUnexpectedResult,
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
        else => return error.TestUnexpectedResult,
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
        else => return error.TestUnexpectedResult,
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
        else => return error.TestUnexpectedResult,
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
        else => return error.TestUnexpectedResult,
    }
}

test "lower: let x = a * 2" {
    const allocator = std.testing.allocator;
    var result = try lowerSource(allocator, "let a = 100mm let x = a * 2");
    defer result.deinit();

    // Should produce: %a : length = 100mm, %x : length = mul %a 2
    try std.testing.expectEqual(2, result.instructions.len);

    const inst = result.instructions[1];
    try std.testing.expectEqualStrings("x", inst.name);
    try std.testing.expectEqual(Type.length, inst.ty);

    switch (inst.rhs) {
        .builtin => |b| {
            try std.testing.expectEqual(Op.mul, b.op);
            try std.testing.expect(b.lhs == .ref);
            try std.testing.expectEqualStrings("a", b.lhs.ref);
            try std.testing.expect(b.rhs == .literal);
            try std.testing.expectEqual(@as(f64, 2.0), b.rhs.literal.number);
        },
        else => return error.TestUnexpectedResult,
    }
}

test "lower: let x = (2 + 2) / 2 flattens to temps" {
    const allocator = std.testing.allocator;
    var result = try lowerSource(allocator, "let x = (2 + 2) / 2");
    defer result.deinit();

    // Should produce: %0 : f64 = add 2 2, %x : f64 = div %0 2
    try std.testing.expectEqual(2, result.instructions.len);

    const temp = result.instructions[0];
    try std.testing.expectEqualStrings("0", temp.name);
    try std.testing.expectEqual(Type.f64, temp.ty);
    switch (temp.rhs) {
        .builtin => |b| {
            try std.testing.expectEqual(Op.add, b.op);
            try std.testing.expect(b.lhs == .literal);
            try std.testing.expectEqual(@as(f64, 2.0), b.lhs.literal.number);
            try std.testing.expect(b.rhs == .literal);
            try std.testing.expectEqual(@as(f64, 2.0), b.rhs.literal.number);
        },
        else => return error.TestUnexpectedResult,
    }

    const inst = result.instructions[1];
    try std.testing.expectEqualStrings("x", inst.name);
    try std.testing.expectEqual(Type.f64, inst.ty);
    switch (inst.rhs) {
        .builtin => |b| {
            try std.testing.expectEqual(Op.div, b.op);
            try std.testing.expect(b.lhs == .ref);
            try std.testing.expectEqualStrings("0", b.lhs.ref);
            try std.testing.expect(b.rhs == .literal);
            try std.testing.expectEqual(@as(f64, 2.0), b.rhs.literal.number);
        },
        else => return error.TestUnexpectedResult,
    }
}

test "lower: simple arithmetic 1 + 2" {
    const allocator = std.testing.allocator;
    var result = try lowerSource(allocator, "let x = 1 + 2");
    defer result.deinit();

    // Single instruction: %x : f64 = add 1 2
    try std.testing.expectEqual(1, result.instructions.len);

    const inst = result.instructions[0];
    try std.testing.expectEqualStrings("x", inst.name);
    try std.testing.expectEqual(Type.f64, inst.ty);
    switch (inst.rhs) {
        .builtin => |b| {
            try std.testing.expectEqual(Op.add, b.op);
        },
        else => return error.TestUnexpectedResult,
    }
}

test "lower: chained 1 + 2 * 3 respects precedence" {
    const allocator = std.testing.allocator;
    var result = try lowerSource(allocator, "let x = 1 + 2 * 3");
    defer result.deinit();

    // Should produce: %0 : f64 = mul 2 3, %x : f64 = add 1 %0
    try std.testing.expectEqual(2, result.instructions.len);

    const temp = result.instructions[0];
    switch (temp.rhs) {
        .builtin => |b| try std.testing.expectEqual(Op.mul, b.op),
        else => return error.TestUnexpectedResult,
    }

    const inst = result.instructions[1];
    try std.testing.expectEqualStrings("x", inst.name);
    switch (inst.rhs) {
        .builtin => |b| try std.testing.expectEqual(Op.add, b.op),
        else => return error.TestUnexpectedResult,
    }
}

test "lower: input head = 100mm" {
    const allocator = std.testing.allocator;
    var result = try lowerSource(allocator, "input head = 100mm");
    defer result.deinit();

    try std.testing.expectEqual(1, result.inputs.len);
    try std.testing.expectEqual(0, result.instructions.len);

    const input = result.inputs[0];
    try std.testing.expectEqualStrings("head", input.name);
    try std.testing.expectEqual(Type.length, input.ty);
    try std.testing.expectEqual(@as(f64, 100.0), input.default.number);
    try std.testing.expectEqual(LengthUnit.mm, input.default.unit.?);
}

test "lower: input with cm unit" {
    const allocator = std.testing.allocator;
    var result = try lowerSource(allocator, "input w = 25cm");
    defer result.deinit();

    try std.testing.expectEqual(1, result.inputs.len);
    const input = result.inputs[0];
    try std.testing.expectEqual(@as(f64, 25.0), input.default.number);
    try std.testing.expectEqual(LengthUnit.cm, input.default.unit.?);
}

test "lower: input f64" {
    const allocator = std.testing.allocator;
    var result = try lowerSource(allocator, "input scale = 42");
    defer result.deinit();

    try std.testing.expectEqual(1, result.inputs.len);
    const input = result.inputs[0];
    try std.testing.expectEqualStrings("scale", input.name);
    try std.testing.expectEqual(Type.f64, input.ty);
    try std.testing.expectEqual(@as(f64, 42.0), input.default.number);
    try std.testing.expectEqual(@as(?LengthUnit, null), input.default.unit);
}

test "lower: input percentage" {
    const allocator = std.testing.allocator;
    var result = try lowerSource(allocator, "input ease = 50%");
    defer result.deinit();

    try std.testing.expectEqual(1, result.inputs.len);
    const input = result.inputs[0];
    try std.testing.expectEqual(Type.percentage, input.ty);
    try std.testing.expectEqual(@as(f64, 50.0), input.default.number);
}

test "lower: mixed inputs and lets" {
    const allocator = std.testing.allocator;
    var result = try lowerSource(allocator, "input head = 100mm let x = head");
    defer result.deinit();

    try std.testing.expectEqual(1, result.inputs.len);
    try std.testing.expectEqual(1, result.instructions.len);

    try std.testing.expectEqualStrings("head", result.inputs[0].name);
    try std.testing.expectEqualStrings("x", result.instructions[0].name);

    switch (result.instructions[0].rhs) {
        .copy => |name| try std.testing.expectEqualStrings("head", name),
        else => return error.TestUnexpectedResult,
    }
}

test "lower: input with arithmetic in let" {
    const allocator = std.testing.allocator;
    var result = try lowerSource(allocator, "input head = 100mm let x = head * 2");
    defer result.deinit();

    try std.testing.expectEqual(1, result.inputs.len);
    try std.testing.expectEqual(1, result.instructions.len);

    const inst = result.instructions[0];
    try std.testing.expectEqualStrings("x", inst.name);
    try std.testing.expectEqual(Type.length, inst.ty);
    switch (inst.rhs) {
        .builtin => |b| {
            try std.testing.expectEqual(Op.mul, b.op);
            try std.testing.expect(b.lhs == .ref);
            try std.testing.expectEqualStrings("head", b.lhs.ref);
        },
        else => return error.TestUnexpectedResult,
    }
}
