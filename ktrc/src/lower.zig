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
/// Derived at comptime via tag names so new non-poison types are mapped
/// automatically without manual updates.
fn mapType(sema_ty: sema.Type) Type {
    if (sema_ty == .poison) unreachable;
    return std.meta.stringToEnum(Type, @tagName(sema_ty)).?;
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

    /// Emit a builtin instruction with a fresh temp name and return a ref to it.
    fn emitBuiltin(self: *Lowerer, op: Op, operands: []const Operand, node_index: ast.NodeIndex) LowerError!Operand {
        const ty = self.nodeType(node_index);
        const name = try self.tempName();
        try self.instructions.append(self.ally, .{
            .name = name,
            .ty = ty,
            .rhs = .{ .builtin = .{ .op = op, .operands = operands } },
        });
        return .{ .ref = name };
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
                const operands = try self.ally.dupe(Operand, &.{ lhs_operand, rhs_operand });
                return self.emitBuiltin(mapOp(node.tag), operands, node_index);
            },
            .fn_call => {
                return try self.lowerFnCall(node_index);
            },
            .root, .let_statement, .input_statement, .fn_def, .param, .return_stmt => unreachable,
        };
    }

    /// Lower a function call expression (e.g. `point(x, y)`, `bezier(p1, p2, p3, p4)`,
    /// or a user-defined function call).
    fn lowerFnCall(self: *Lowerer, node_index: ast.NodeIndex) LowerError!Operand {
        const node = self.tree.nodes.get(node_index);
        const fn_name = self.tree.tokenSlice(node.main_token);
        const args = self.tree.callArgs(node_index);

        // Lower each argument to an operand.
        const operands = try self.ally.alloc(Operand, args.len);
        for (args, 0..) |arg_idx, i| {
            operands[i] = try self.lowerExpr(arg_idx);
        }

        // Check builtins first.
        if (ir.builtin_sigs.get(fn_name)) |sig| {
            return self.emitBuiltin(sig.op, operands, node_index);
        }

        // User-defined function call.
        const ty = self.nodeType(node_index);
        const name = try self.tempName();
        try self.instructions.append(self.ally, .{
            .name = name,
            .ty = ty,
            .rhs = .{ .call = .{
                .func = try self.ally.dupe(u8, fn_name),
                .args = operands,
            } },
        });
        return .{ .ref = name };
    }

    /// Lower a function definition into an `ir.FnDef`.
    fn lowerFnDef(self: *Lowerer, fn_def_index: ast.NodeIndex) LowerError!ir.FnDef {
        const fn_node = self.tree.nodes.get(fn_def_index);
        const fn_name_slice = self.tree.tokenSlice(fn_node.main_token + 1);
        const fn_name = try self.ally.dupe(u8, fn_name_slice);

        const param_nodes = self.tree.fnDefParams(fn_def_index);
        const body_nodes = self.tree.fnDefBody(fn_def_index);
        const return_expr = self.tree.fnDefReturn(fn_def_index);

        // Build IR params from the sema function signature.
        const fn_sig = self.sema_result.functions.get(fn_name_slice).?;
        const params = try self.ally.alloc(ir.Param, param_nodes.len);
        for (fn_sig.params, 0..) |param_info, i| {
            params[i] = .{
                .name = try self.ally.dupe(u8, param_info.name),
                .ty = mapType(param_info.ty),
            };
        }

        // Create a sub-lowerer for the function body. Only `instructions`
        // and `temp_counter` are used; `inputs` is unused but required by
        // the shared Lowerer struct (avoids a separate BodyLowerer type).
        var sub = Lowerer{
            .tree = self.tree,
            .sema_result = self.sema_result,
            .ally = self.ally,
            .inputs = .{},
            .instructions = .{},
            .temp_counter = 0,
        };

        // Lower body let-statements using AST node types directly.
        for (body_nodes) |stmt_idx| {
            const stmt_node = self.tree.nodes.get(stmt_idx);
            if (stmt_node.tag == .let_statement) {
                const name = self.tree.tokenSlice(stmt_node.main_token + 1);
                const sema_ty = self.sema_result.node_types[stmt_node.data.lhs];
                const sym = sema.Symbol{
                    .ty = sema_ty,
                    .node = stmt_idx,
                    .kind = .let_binding,
                };
                try sub.lowerLet(name, sym);
            }
        }

        // Lower the return expression.
        const ret_operand = try sub.lowerExpr(return_expr);

        // Determine the return binding name.
        const ret_name = switch (ret_operand) {
            .ref => |r| try self.ally.dupe(u8, r),
            .literal => |v| blk: {
                // Need to emit a constant instruction for the literal.
                const ret_ty = self.nodeType(return_expr);
                const tmp = try sub.tempName();
                try sub.instructions.append(self.ally, .{
                    .name = tmp,
                    .ty = ret_ty,
                    .rhs = .{ .constant = v },
                });
                break :blk tmp;
            },
        };

        // Infer return type.
        const ret_ty = mapType(self.sema_result.node_types[return_expr]);

        return .{
            .name = fn_name,
            .params = params,
            .ret_ty = ret_ty,
            .body = try sub.instructions.toOwnedSlice(self.ally),
            .ret = ret_name,
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

    var fn_defs = std.ArrayListUnmanaged(ir.FnDef){};

    // Iterate root AST statements in order to preserve topo-sort.
    const statements = tree.rootStatements(0);
    for (statements) |stmt_index| {
        const node = tree.nodes.get(stmt_index);
        switch (node.tag) {
            .input_statement => {
                const name = tree.tokenSlice(node.main_token + 1);
                const sym = sema_result.symbols.get(name).?;
                try l.lowerInput(name, sym);
            },
            .let_statement => {
                const name = tree.tokenSlice(node.main_token + 1);
                const sym = sema_result.symbols.get(name).?;
                try l.lowerLet(name, sym);
            },
            .fn_def => {
                const fn_def = try l.lowerFnDef(stmt_index);
                try fn_defs.append(ally, fn_def);
            },
            else => {},
        }
    }

    return .{
        .version = 1,
        .inputs = try l.inputs.toOwnedSlice(ally),
        .functions = try fn_defs.toOwnedSlice(ally),
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
            try std.testing.expect(b.operands[0] == .ref);
            try std.testing.expectEqualStrings("a", b.operands[0].ref);
            try std.testing.expect(b.operands[1] == .literal);
            try std.testing.expectEqual(@as(f64, 2.0), b.operands[1].literal.number);
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
            try std.testing.expect(b.operands[0] == .literal);
            try std.testing.expectEqual(@as(f64, 2.0), b.operands[0].literal.number);
            try std.testing.expect(b.operands[1] == .literal);
            try std.testing.expectEqual(@as(f64, 2.0), b.operands[1].literal.number);
        },
        else => return error.TestUnexpectedResult,
    }

    const inst = result.instructions[1];
    try std.testing.expectEqualStrings("x", inst.name);
    try std.testing.expectEqual(Type.f64, inst.ty);
    switch (inst.rhs) {
        .builtin => |b| {
            try std.testing.expectEqual(Op.div, b.op);
            try std.testing.expect(b.operands[0] == .ref);
            try std.testing.expectEqualStrings("0", b.operands[0].ref);
            try std.testing.expect(b.operands[1] == .literal);
            try std.testing.expectEqual(@as(f64, 2.0), b.operands[1].literal.number);
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
            try std.testing.expect(b.operands[0] == .ref);
            try std.testing.expectEqualStrings("head", b.operands[0].ref);
        },
        else => return error.TestUnexpectedResult,
    }
}

test "lower: point(100mm, 50mm)" {
    const allocator = std.testing.allocator;
    var result = try lowerSource(allocator, "let p = point(100mm, 50mm)");
    defer result.deinit();

    try std.testing.expectEqual(1, result.instructions.len);
    const inst = result.instructions[0];
    try std.testing.expectEqualStrings("p", inst.name);
    try std.testing.expectEqual(Type.point, inst.ty);

    switch (inst.rhs) {
        .builtin => |b| {
            try std.testing.expectEqual(Op.point, b.op);
            try std.testing.expectEqual(2, b.operands.len);
            try std.testing.expect(b.operands[0] == .literal);
            try std.testing.expectEqual(@as(f64, 100.0), b.operands[0].literal.number);
            try std.testing.expectEqual(LengthUnit.mm, b.operands[0].literal.unit.?);
            try std.testing.expect(b.operands[1] == .literal);
            try std.testing.expectEqual(@as(f64, 50.0), b.operands[1].literal.number);
        },
        else => return error.TestUnexpectedResult,
    }
}

test "lower: point with ref args" {
    const allocator = std.testing.allocator;
    var result = try lowerSource(allocator, "input head = 100mm let p = point(head, 0mm)");
    defer result.deinit();

    try std.testing.expectEqual(1, result.inputs.len);
    try std.testing.expectEqual(1, result.instructions.len);

    const inst = result.instructions[0];
    try std.testing.expectEqualStrings("p", inst.name);
    try std.testing.expectEqual(Type.point, inst.ty);

    switch (inst.rhs) {
        .builtin => |b| {
            try std.testing.expectEqual(Op.point, b.op);
            try std.testing.expect(b.operands[0] == .ref);
            try std.testing.expectEqualStrings("head", b.operands[0].ref);
            try std.testing.expect(b.operands[1] == .literal);
            try std.testing.expectEqual(@as(f64, 0.0), b.operands[1].literal.number);
        },
        else => return error.TestUnexpectedResult,
    }
}

test "lower: point with expression args" {
    const allocator = std.testing.allocator;
    var result = try lowerSource(allocator, "let a = 100mm let p = point(a * 2, a / 3)");
    defer result.deinit();

    // Should produce: %a, %0 (temp for a*2), %1 (temp for a/3), %p (point %0 %1)
    try std.testing.expectEqual(4, result.instructions.len);

    const inst = result.instructions[3];
    try std.testing.expectEqualStrings("p", inst.name);
    try std.testing.expectEqual(Type.point, inst.ty);

    switch (inst.rhs) {
        .builtin => |b| {
            try std.testing.expectEqual(Op.point, b.op);
            try std.testing.expect(b.operands[0] == .ref);
            try std.testing.expect(b.operands[1] == .ref);
        },
        else => return error.TestUnexpectedResult,
    }
}

test "lower: bezier with ref args" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 =
        \\let p1 = point(0mm, 0mm)
        \\let p2 = point(100mm, 0mm)
        \\let p3 = point(100mm, 100mm)
        \\let p4 = point(0mm, 100mm)
        \\let c = bezier(p1, p2, p3, p4)
    ;
    var result = try lowerSource(allocator, source);
    defer result.deinit();

    // 4 point instructions + 1 bezier instruction = 5
    try std.testing.expectEqual(5, result.instructions.len);

    const inst = result.instructions[4];
    try std.testing.expectEqualStrings("c", inst.name);
    try std.testing.expectEqual(Type.bezier, inst.ty);

    switch (inst.rhs) {
        .builtin => |b| {
            try std.testing.expectEqual(Op.bezier, b.op);
            try std.testing.expectEqual(4, b.operands.len);
            try std.testing.expect(b.operands[0] == .ref);
            try std.testing.expectEqualStrings("p1", b.operands[0].ref);
            try std.testing.expect(b.operands[1] == .ref);
            try std.testing.expectEqualStrings("p2", b.operands[1].ref);
            try std.testing.expect(b.operands[2] == .ref);
            try std.testing.expectEqualStrings("p3", b.operands[2].ref);
            try std.testing.expect(b.operands[3] == .ref);
            try std.testing.expectEqualStrings("p4", b.operands[3].ref);
        },
        else => return error.TestUnexpectedResult,
    }
}

test "lower: line with literal point args" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 =
        \\let a = point(0mm, 0mm)
        \\let b = point(100mm, 50mm)
        \\let c = line(a, b)
    ;
    var result = try lowerSource(allocator, source);
    defer result.deinit();

    // 2 point instructions + 1 line instruction = 3
    try std.testing.expectEqual(3, result.instructions.len);

    const inst = result.instructions[2];
    try std.testing.expectEqualStrings("c", inst.name);
    try std.testing.expectEqual(Type.line, inst.ty);

    switch (inst.rhs) {
        .builtin => |b| {
            try std.testing.expectEqual(Op.line, b.op);
            try std.testing.expectEqual(2, b.operands.len);
            try std.testing.expect(b.operands[0] == .ref);
            try std.testing.expectEqualStrings("a", b.operands[0].ref);
            try std.testing.expect(b.operands[1] == .ref);
            try std.testing.expectEqualStrings("b", b.operands[1].ref);
        },
        else => return error.TestUnexpectedResult,
    }
}

test "lower: line with ref args" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 =
        \\input head = 100mm
        \\let a = point(head, 0mm)
        \\let b = point(0mm, head)
        \\let c = line(a, b)
    ;
    var result = try lowerSource(allocator, source);
    defer result.deinit();

    try std.testing.expectEqual(1, result.inputs.len);
    // 2 point instructions + 1 line instruction = 3
    try std.testing.expectEqual(3, result.instructions.len);

    const inst = result.instructions[2];
    try std.testing.expectEqualStrings("c", inst.name);
    try std.testing.expectEqual(Type.line, inst.ty);

    switch (inst.rhs) {
        .builtin => |b| {
            try std.testing.expectEqual(Op.line, b.op);
            try std.testing.expect(b.operands[0] == .ref);
            try std.testing.expectEqualStrings("a", b.operands[0].ref);
            try std.testing.expect(b.operands[1] == .ref);
            try std.testing.expectEqualStrings("b", b.operands[1].ref);
        },
        else => return error.TestUnexpectedResult,
    }
}

test "lower: line with expression args" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 =
        \\let a = point(0mm, 0mm)
        \\let b = point(100mm * 2, 50mm / 2)
        \\let c = line(a, b)
    ;
    var result = try lowerSource(allocator, source);
    defer result.deinit();

    // a: point, temp0: mul, temp1: div, b: point, c: line = 5
    try std.testing.expectEqual(5, result.instructions.len);

    const inst = result.instructions[4];
    try std.testing.expectEqualStrings("c", inst.name);
    try std.testing.expectEqual(Type.line, inst.ty);
}

test "lower: fn_def simple" {
    const allocator = std.testing.allocator;
    var result = try lowerSource(allocator, "fn double(x: f64) { return x * 2 }");
    defer result.deinit();

    try std.testing.expectEqual(0, result.instructions.len);
    try std.testing.expectEqual(1, result.functions.len);

    const fn_def = result.functions[0];
    try std.testing.expectEqualStrings("double", fn_def.name);
    try std.testing.expectEqual(Type.f64, fn_def.ret_ty);
    try std.testing.expectEqual(1, fn_def.params.len);
    try std.testing.expectEqualStrings("x", fn_def.params[0].name);
    try std.testing.expectEqual(Type.f64, fn_def.params[0].ty);

    // Body: %0 : f64 = mul %x 2, ret = "0"
    try std.testing.expectEqual(1, fn_def.body.len);
    switch (fn_def.body[0].rhs) {
        .builtin => |b| {
            try std.testing.expectEqual(Op.mul, b.op);
            try std.testing.expectEqualStrings("x", b.operands[0].ref);
            try std.testing.expectEqual(@as(f64, 2.0), b.operands[1].literal.number);
        },
        else => return error.TestUnexpectedResult,
    }
    try std.testing.expectEqualStrings("0", fn_def.ret);
}

test "lower: fn_def with body" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 =
        \\fn half(x: length) {
        \\  let result = x / 2
        \\  return result
        \\}
    ;
    var result = try lowerSource(allocator, source);
    defer result.deinit();

    try std.testing.expectEqual(1, result.functions.len);
    const fn_def = result.functions[0];
    try std.testing.expectEqualStrings("half", fn_def.name);
    try std.testing.expectEqual(Type.length, fn_def.ret_ty);

    // Body: %result : length = div %x 2, ret = "result"
    try std.testing.expectEqual(1, fn_def.body.len);
    try std.testing.expectEqualStrings("result", fn_def.body[0].name);
    try std.testing.expectEqualStrings("result", fn_def.ret);
}

test "lower: fn call user-defined" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 =
        \\fn double(x: f64) { return x * 2 }
        \\let y = double(5)
    ;
    var result = try lowerSource(allocator, source);
    defer result.deinit();

    try std.testing.expectEqual(1, result.functions.len);
    try std.testing.expectEqual(1, result.instructions.len);

    const inst = result.instructions[0];
    try std.testing.expectEqualStrings("y", inst.name);
    try std.testing.expectEqual(Type.f64, inst.ty);

    switch (inst.rhs) {
        .call => |c| {
            try std.testing.expectEqualStrings("double", c.func);
            try std.testing.expectEqual(1, c.args.len);
            try std.testing.expectEqual(@as(f64, 5.0), c.args[0].literal.number);
        },
        else => return error.TestUnexpectedResult,
    }
}

test "lower: fn def with input ref and call" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 =
        \\input head = 100mm
        \\fn scale_head(factor: f64) { return head * factor }
        \\let y = scale_head(2)
    ;
    var result = try lowerSource(allocator, source);
    defer result.deinit();

    try std.testing.expectEqual(1, result.inputs.len);
    try std.testing.expectEqual(1, result.functions.len);
    try std.testing.expectEqual(1, result.instructions.len);

    const fn_def = result.functions[0];
    try std.testing.expectEqualStrings("scale_head", fn_def.name);
    try std.testing.expectEqual(Type.length, fn_def.ret_ty);

    switch (result.instructions[0].rhs) {
        .call => |c| {
            try std.testing.expectEqualStrings("scale_head", c.func);
        },
        else => return error.TestUnexpectedResult,
    }
}

test "lower: fn_def return literal" {
    const allocator = std.testing.allocator;
    var result = try lowerSource(allocator, "fn zero() { return 42 }");
    defer result.deinit();

    try std.testing.expectEqual(1, result.functions.len);
    const fn_def = result.functions[0];
    try std.testing.expectEqualStrings("zero", fn_def.name);
    try std.testing.expectEqual(Type.f64, fn_def.ret_ty);
    try std.testing.expectEqual(0, fn_def.params.len);

    // Should have a body instruction for the literal.
    try std.testing.expectEqual(1, fn_def.body.len);
    switch (fn_def.body[0].rhs) {
        .constant => |v| try std.testing.expectEqual(@as(f64, 42.0), v.number),
        else => return error.TestUnexpectedResult,
    }
    try std.testing.expectEqualStrings(fn_def.ret, fn_def.body[0].name);
}
