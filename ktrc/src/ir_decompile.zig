const std = @import("std");
const ir = @import("ir.zig");
const Ir = ir.Ir;
const Inst = ir.Inst;
const Value = ir.Value;
const Type = ir.Type;
const Op = ir.Op;
const Operand = ir.Operand;

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

/// Map an IR op to a ktr infix operator string.
/// Only valid for non-constructor ops.
fn opToInfix(op: Op) []const u8 {
    std.debug.assert(!op.isConstructor());
    return switch (op) {
        .add => " + ",
        .sub => " - ",
        .mul => " * ",
        .div => " / ",
        .point, .bezier, .line => unreachable,
    };
}

/// Build a use-count map: how many times each %name is referenced as an operand.
fn buildUseCounts(allocator: std.mem.Allocator, instructions: []const Inst) !std.StringHashMap(u32) {
    var counts = std.StringHashMap(u32).init(allocator);
    for (instructions) |inst| {
        switch (inst.rhs) {
            .copy => |name| {
                const entry = try counts.getOrPut(name);
                if (!entry.found_existing) entry.value_ptr.* = 0;
                entry.value_ptr.* += 1;
            },
            .builtin => |b| {
                for (b.operands) |operand| {
                    if (operand == .ref) {
                        const entry = try counts.getOrPut(operand.ref);
                        if (!entry.found_existing) entry.value_ptr.* = 0;
                        entry.value_ptr.* += 1;
                    }
                }
            },
            .call => |c| {
                for (c.args) |arg| {
                    if (arg == .ref) {
                        const entry = try counts.getOrPut(arg.ref);
                        if (!entry.found_existing) entry.value_ptr.* = 0;
                        entry.value_ptr.* += 1;
                    }
                }
            },
            .constant => {},
        }
    }
    return counts;
}

/// Build a map from instruction name to instruction for temp inlining lookups.
fn buildInstMap(allocator: std.mem.Allocator, instructions: []const Inst) !std.StringHashMap(Inst) {
    var map = std.StringHashMap(Inst).init(allocator);
    for (instructions) |inst| {
        try map.put(inst.name, inst);
    }
    return map;
}

fn opPrecedence(op: Op) u8 {
    std.debug.assert(!op.isConstructor());
    return switch (op) {
        .add, .sub => 1,
        .mul, .div => 2,
        .point, .bezier, .line => unreachable,
    };
}

/// Determine if parentheses are needed when inlining a child expression.
fn needsParentheses(child_op: Op, parent_op: ?Op, is_rhs: bool) bool {
    const parent = parent_op orelse return false;
    const child_prec = opPrecedence(child_op);
    const parent_prec = opPrecedence(parent);
    if (child_prec < parent_prec) return true;
    // Same precedence on the right side of a non-commutative op needs parens:
    // a - (b + c) or a / (b * c)
    if (child_prec == parent_prec and is_rhs and (parent == .sub or parent == .div)) return true;
    return false;
}

/// Holds pre-computed analysis for reconstructing ktr source from flat IR.
const Decompiler = struct {
    inst_map: std.StringHashMap(Inst),
    use_counts: std.StringHashMap(u32),

    fn init(allocator: std.mem.Allocator, instructions: []const Inst) !Decompiler {
        return .{
            .inst_map = try buildInstMap(allocator, instructions),
            .use_counts = try buildUseCounts(allocator, instructions),
        };
    }

    fn deinit(self: *Decompiler) void {
        self.inst_map.deinit();
        self.use_counts.deinit();
    }

    fn isSingleUseTemp(self: *const Decompiler, name: []const u8) bool {
        return ir.isTemp(name) and (self.use_counts.get(name) orelse 0) == 1;
    }

    /// Write a bare literal value (number with optional unit suffix).
    fn writeLiteral(writer: anytype, v: Value) !void {
        try v.writeNumber(writer);
        if (v.unit) |u| try writer.writeAll(u.toStr());
    }

    /// Write a builtin op inline. Constructor ops use `name(arg, ...)` syntax;
    /// infix ops use `lhs op rhs` syntax.
    fn writeBuiltinInline(self: *const Decompiler, writer: anytype, b: Inst.Builtin, parent_op: ?Op, is_rhs: bool) @TypeOf(writer).Error!void {
        if (b.op.isConstructor()) {
            try writer.writeAll(b.op.toStr());
            try writer.writeByte('(');
            for (b.operands, 0..) |operand, i| {
                if (i > 0) try writer.writeAll(", ");
                try self.writeExpr(writer, operand, null, false);
            }
            try writer.writeByte(')');
        } else {
            const needs_parens = needsParentheses(b.op, parent_op, is_rhs);
            if (needs_parens) try writer.writeByte('(');
            try self.writeExpr(writer, b.operands[0], b.op, false);
            try writer.writeAll(opToInfix(b.op));
            try self.writeExpr(writer, b.operands[1], b.op, true);
            if (needs_parens) try writer.writeByte(')');
        }
    }

    /// Write a user-defined function call inline: `func_name(arg1, arg2, ...)`.
    fn writeCallInline(self: *const Decompiler, writer: anytype, c: Inst.Call) @TypeOf(writer).Error!void {
        try writer.writeAll(c.func);
        try writer.writeByte('(');
        for (c.args, 0..) |arg, i| {
            if (i > 0) try writer.writeAll(", ");
            try self.writeExpr(writer, arg, null, false);
        }
        try writer.writeByte(')');
    }

    /// Write an operand in ktr source form, potentially inlining single-use temps.
    fn writeExpr(self: *const Decompiler, writer: anytype, operand: Operand, parent_op: ?Op, is_rhs: bool) !void {
        switch (operand) {
            .literal => |v| try writeLiteral(writer, v),
            .ref => |name| {
                // If this ref points to a single-use temp, inline its expression.
                if (self.isSingleUseTemp(name)) {
                    if (self.inst_map.get(name)) |temp_inst| {
                        switch (temp_inst.rhs) {
                            .builtin => |b| {
                                try self.writeBuiltinInline(writer, b, parent_op, is_rhs);
                                return;
                            },
                            .constant => |v| {
                                try writeLiteral(writer, v);
                                return;
                            },
                            .copy => |copy_name| {
                                try writer.writeAll(copy_name);
                                return;
                            },
                            .call => |c| {
                                try self.writeCallInline(writer, c);
                                return;
                            },
                        }
                    }
                }
                try writer.writeAll(name);
            },
        }
    }
};

/// Map an IR type to its ktr source name.
fn irTypeToKtrName(ty: Type) []const u8 {
    return ty.toStr();
}

/// Write instructions as ktr let-bindings using a decompiler for temp inlining.
fn writeInstructions(dc: *const Decompiler, instructions: []const Inst, writer: anytype, first: *bool) !void {
    for (instructions) |inst| {
        // Skip single-use temps -- they will be inlined.
        if (dc.isSingleUseTemp(inst.name)) continue;

        if (!first.*) try writer.writeByte('\n');
        first.* = false;

        try writer.print("let {s} = ", .{inst.name});

        switch (inst.rhs) {
            .constant => |v| try writeKtrValue(writer, v, inst.ty),
            .copy => |name| try writer.writeAll(name),
            .builtin => |b| try dc.writeBuiltinInline(writer, b, null, false),
            .call => |c| try dc.writeCallInline(writer, c),
        }
    }
}

/// Reconstruct `.ktr` source from an `Ir`.
///
/// Input entries are emitted as `input name = value`. Instructions that are
/// single-use compiler temporaries (numeric names used exactly once) are
/// inlined into their parent expression. All other instructions emit a `let`
/// binding.
pub fn decompile(allocator: std.mem.Allocator, ir_data: Ir, writer: anytype) !void {
    var dc = try Decompiler.init(allocator, ir_data.instructions);
    defer dc.deinit();

    var first = true;

    for (ir_data.inputs) |input| {
        if (!first) try writer.writeByte('\n');
        first = false;

        try writer.print("input {s} = ", .{input.name});
        try writeKtrValue(writer, input.default, input.ty);
    }

    // Emit function definitions.
    for (ir_data.functions) |fn_def| {
        if (!first) try writer.writeByte('\n');
        first = false;

        // fn name(param1: type, param2: type) {
        try writer.print("fn {s}(", .{fn_def.name});
        for (fn_def.params, 0..) |param, i| {
            if (i > 0) try writer.writeAll(", ");
            try writer.print("{s}: {s}", .{ param.name, irTypeToKtrName(param.ty) });
        }
        try writer.writeAll(") {");

        // Build a scoped decompiler for the function body.
        var fn_dc = try Decompiler.init(allocator, fn_def.body);
        defer fn_dc.deinit();

        // Determine if the ret binding should be inlined into the return expression.
        // Only inline if it's a compiler-generated temp.
        const inline_ret = ir.isTemp(fn_def.ret);

        // Body let-statements.
        for (fn_def.body) |body_inst| {
            if (fn_dc.isSingleUseTemp(body_inst.name)) continue;

            // Skip the return binding if we're going to inline it.
            if (inline_ret and std.mem.eql(u8, body_inst.name, fn_def.ret)) continue;

            try writer.print("\n  let {s} = ", .{body_inst.name});
            switch (body_inst.rhs) {
                .constant => |v| try writeKtrValue(writer, v, body_inst.ty),
                .copy => |name| try writer.writeAll(name),
                .builtin => |b| try fn_dc.writeBuiltinInline(writer, b, null, false),
                .call => |c| try fn_dc.writeCallInline(writer, c),
            }
        }

        // return expression.
        try writer.writeAll("\n  return ");
        if (inline_ret) {
            // Inline the return instruction's expression.
            if (fn_dc.inst_map.get(fn_def.ret)) |ret_inst| {
                switch (ret_inst.rhs) {
                    .constant => |v| try writeKtrValue(writer, v, ret_inst.ty),
                    .copy => |name| try writer.writeAll(name),
                    .builtin => |b| try fn_dc.writeBuiltinInline(writer, b, null, false),
                    .call => |c| try fn_dc.writeCallInline(writer, c),
                }
            } else {
                try writer.writeAll(fn_def.ret);
            }
        } else {
            // Named binding -- just reference it.
            try writer.writeAll(fn_def.ret);
        }

        try writer.writeAll("\n}");
    }

    try writeInstructions(&dc, ir_data.instructions, writer, &first);

    // Trailing newline if there was any output.
    const has_content = ir_data.inputs.len > 0 or ir_data.functions.len > 0 or ir_data.instructions.len > 0;
    if (has_content) {
        try writer.writeByte('\n');
    }
}

// --- Tests ---

const parser = @import("parser.zig");
const sema = @import("sema.zig");
const lower = @import("lower.zig");

fn decompileToString(allocator: std.mem.Allocator, ir_data: Ir) ![]const u8 {
    var buf: std.ArrayListUnmanaged(u8) = .{};
    errdefer buf.deinit(allocator);
    try decompile(allocator, ir_data, buf.writer(allocator));
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

/// Source -> lower -> decompile -> re-parse -> sema -> re-lower, then assert
/// the two Ir representations are structurally identical.
fn expectDecompileRoundtrip(source: [:0]const u8) !void {
    const allocator = std.testing.allocator;

    var tree1 = try parser.parse(allocator, source);
    defer tree1.deinit();

    var sem1 = try sema.analyze(allocator, &tree1);
    defer sem1.deinit();

    var ir1 = try lower.lower(allocator, &tree1, &sem1);
    defer ir1.deinit();

    var buf: std.ArrayListUnmanaged(u8) = .{};
    defer buf.deinit(allocator);
    try decompile(allocator, ir1, buf.writer(allocator));
    const ktr_text = try buf.toOwnedSlice(allocator);
    defer allocator.free(ktr_text);

    const ktr_z = try allocator.dupeZ(u8, ktr_text);
    defer allocator.free(ktr_z);

    var tree2 = try parser.parse(allocator, ktr_z);
    defer tree2.deinit();

    var sem2 = try sema.analyze(allocator, &tree2);
    defer sem2.deinit();

    try std.testing.expect(!sem2.hasErrors());

    var ir2 = try lower.lower(allocator, &tree2, &sem2);
    defer ir2.deinit();

    try std.testing.expect(ir1.eql(ir2));
}

test "decompile roundtrip: source -> lower -> decompile -> re-lower -> compare" {
    try expectDecompileRoundtrip("let a = 100mm\nlet b = 50%\nlet c = 42\nlet d = a");
}

test "decompile: simple arithmetic" {
    const allocator = std.testing.allocator;
    var arena = std.heap.ArenaAllocator.init(allocator);
    const ally = arena.allocator();

    const insts = try ally.alloc(Inst, 2);
    insts[0] = .{
        .name = try ally.dupe(u8, "a"),
        .ty = .length,
        .rhs = .{ .constant = .{ .number = 100.0, .unit = .mm } },
    };
    insts[1] = .{
        .name = try ally.dupe(u8, "x"),
        .ty = .length,
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

    const output = try decompileToString(allocator, ir_data);
    defer allocator.free(output);

    try std.testing.expectEqualStrings("let a = 100mm\nlet x = a * 2\n", output);
}

test "decompile: inlines single-use temps" {
    const allocator = std.testing.allocator;
    var arena = std.heap.ArenaAllocator.init(allocator);
    const ally = arena.allocator();

    // IR for: let x = (2 + 2) / 2
    // %0 : f64 = add 2 2
    // %x : f64 = div %0 2
    const insts = try ally.alloc(Inst, 2);
    insts[0] = .{
        .name = try ally.dupe(u8, "0"),
        .ty = .f64,
        .rhs = .{ .builtin = .{
            .op = .add,
            .operands = try ally.dupe(Operand, &.{
                Operand{ .literal = .{ .number = 2.0, .unit = null } },
                Operand{ .literal = .{ .number = 2.0, .unit = null } },
            }),
        } },
    };
    insts[1] = .{
        .name = try ally.dupe(u8, "x"),
        .ty = .f64,
        .rhs = .{ .builtin = .{
            .op = .div,
            .operands = try ally.dupe(Operand, &.{
                Operand{ .ref = try ally.dupe(u8, "0") },
                Operand{ .literal = .{ .number = 2.0, .unit = null } },
            }),
        } },
    };

    var ir_data = Ir{ .instructions = insts, .arena = arena };
    defer ir_data.deinit();

    const output = try decompileToString(allocator, ir_data);
    defer allocator.free(output);

    // The temp %0 should be inlined, and since add has lower precedence than div,
    // it should be parenthesized.
    try std.testing.expectEqualStrings("let x = (2 + 2) / 2\n", output);
}

test "decompile roundtrip: arithmetic" {
    try expectDecompileRoundtrip("let a = 100mm\nlet x = a * 2");
}

test "decompile roundtrip: grouped expression" {
    try expectDecompileRoundtrip("let x = (2 + 2) / 2");
}

test "decompile: input declaration" {
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

    const output = try decompileToString(allocator, ir_data);
    defer allocator.free(output);

    try std.testing.expectEqualStrings("input head = 100mm\n", output);
}

test "decompile: input with percentage" {
    const allocator = std.testing.allocator;
    var arena = std.heap.ArenaAllocator.init(allocator);
    const ally = arena.allocator();

    const inputs = try ally.alloc(ir.Input, 1);
    inputs[0] = .{
        .name = try ally.dupe(u8, "ease"),
        .ty = .percentage,
        .default = .{ .number = 50.0, .unit = null },
    };

    var ir_data = Ir{ .inputs = inputs, .instructions = &.{}, .arena = arena };
    defer ir_data.deinit();

    const output = try decompileToString(allocator, ir_data);
    defer allocator.free(output);

    try std.testing.expectEqualStrings("input ease = 50%\n", output);
}

test "decompile: input before let" {
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

    const output = try decompileToString(allocator, ir_data);
    defer allocator.free(output);

    try std.testing.expectEqualStrings("input head = 100mm\nlet x = head\n", output);
}

test "decompile roundtrip: input" {
    try expectDecompileRoundtrip("input head = 100mm\nlet x = head * 2");
}

test "decompile: point constructor" {
    const allocator = std.testing.allocator;
    var arena = std.heap.ArenaAllocator.init(allocator);
    const ally = arena.allocator();

    const insts = try ally.alloc(Inst, 1);
    insts[0] = .{
        .name = try ally.dupe(u8, "p"),
        .ty = .point,
        .rhs = .{ .builtin = .{
            .op = .point,
            .operands = try ally.dupe(Operand, &.{
                Operand{ .literal = .{ .number = 100.0, .unit = .mm } },
                Operand{ .literal = .{ .number = 50.0, .unit = .mm } },
            }),
        } },
    };

    var ir_data = Ir{ .instructions = insts, .arena = arena };
    defer ir_data.deinit();

    const output = try decompileToString(allocator, ir_data);
    defer allocator.free(output);

    try std.testing.expectEqualStrings("let p = point(100mm, 50mm)\n", output);
}

test "decompile: point with ref args" {
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
        .name = try ally.dupe(u8, "p"),
        .ty = .point,
        .rhs = .{ .builtin = .{
            .op = .point,
            .operands = try ally.dupe(Operand, &.{
                Operand{ .ref = try ally.dupe(u8, "x") },
                Operand{ .literal = .{ .number = 0.0, .unit = .mm } },
            }),
        } },
    };

    var ir_data = Ir{ .instructions = insts, .arena = arena };
    defer ir_data.deinit();

    const output = try decompileToString(allocator, ir_data);
    defer allocator.free(output);

    try std.testing.expectEqualStrings("let x = 100mm\nlet p = point(x, 0mm)\n", output);
}

test "decompile: point inlines single-use temp args" {
    const allocator = std.testing.allocator;
    var arena = std.heap.ArenaAllocator.init(allocator);
    const ally = arena.allocator();

    // IR for: let p = point(a * 2, 0mm)
    // %0 : length = mul %a 2
    // %p : point = point %0 0mm
    const insts = try ally.alloc(Inst, 3);
    insts[0] = .{
        .name = try ally.dupe(u8, "a"),
        .ty = .length,
        .rhs = .{ .constant = .{ .number = 100.0, .unit = .mm } },
    };
    insts[1] = .{
        .name = try ally.dupe(u8, "0"),
        .ty = .length,
        .rhs = .{ .builtin = .{
            .op = .mul,
            .operands = try ally.dupe(Operand, &.{
                Operand{ .ref = try ally.dupe(u8, "a") },
                Operand{ .literal = .{ .number = 2.0, .unit = null } },
            }),
        } },
    };
    insts[2] = .{
        .name = try ally.dupe(u8, "p"),
        .ty = .point,
        .rhs = .{ .builtin = .{
            .op = .point,
            .operands = try ally.dupe(Operand, &.{
                Operand{ .ref = try ally.dupe(u8, "0") },
                Operand{ .literal = .{ .number = 0.0, .unit = .mm } },
            }),
        } },
    };

    var ir_data = Ir{ .instructions = insts, .arena = arena };
    defer ir_data.deinit();

    const output = try decompileToString(allocator, ir_data);
    defer allocator.free(output);

    try std.testing.expectEqualStrings("let a = 100mm\nlet p = point(a * 2, 0mm)\n", output);
}

test "decompile roundtrip: point constructor" {
    try expectDecompileRoundtrip("let p = point(100mm, 50mm)");
}

test "decompile roundtrip: point with ref args" {
    try expectDecompileRoundtrip("input head = 100mm\nlet p = point(head, 0mm)");
}

test "decompile roundtrip: point with expression args" {
    try expectDecompileRoundtrip("input head = 100mm\nlet p = point(head * 2, head / 3)");
}

test "decompile roundtrip: bezier constructor" {
    try expectDecompileRoundtrip(
        \\let p1 = point(0mm, 0mm)
        \\let p2 = point(100mm, 0mm)
        \\let p3 = point(100mm, 100mm)
        \\let p4 = point(0mm, 100mm)
        \\let c = bezier(p1, p2, p3, p4)
    );
}

test "decompile: line constructor" {
    const allocator = std.testing.allocator;
    var arena = std.heap.ArenaAllocator.init(allocator);
    const ally = arena.allocator();

    const insts = try ally.alloc(Inst, 3);
    insts[0] = .{
        .name = try ally.dupe(u8, "a"),
        .ty = .point,
        .rhs = .{ .builtin = .{
            .op = .point,
            .operands = try ally.dupe(Operand, &.{
                Operand{ .literal = .{ .number = 0.0, .unit = .mm } },
                Operand{ .literal = .{ .number = 0.0, .unit = .mm } },
            }),
        } },
    };
    insts[1] = .{
        .name = try ally.dupe(u8, "b"),
        .ty = .point,
        .rhs = .{ .builtin = .{
            .op = .point,
            .operands = try ally.dupe(Operand, &.{
                Operand{ .literal = .{ .number = 100.0, .unit = .mm } },
                Operand{ .literal = .{ .number = 50.0, .unit = .mm } },
            }),
        } },
    };
    insts[2] = .{
        .name = try ally.dupe(u8, "c"),
        .ty = .line,
        .rhs = .{ .builtin = .{
            .op = .line,
            .operands = try ally.dupe(Operand, &.{
                Operand{ .ref = try ally.dupe(u8, "a") },
                Operand{ .ref = try ally.dupe(u8, "b") },
            }),
        } },
    };

    var ir_data = Ir{ .instructions = insts, .arena = arena };
    defer ir_data.deinit();

    const output = try decompileToString(allocator, ir_data);
    defer allocator.free(output);

    const expected =
        \\let a = point(0mm, 0mm)
        \\let b = point(100mm, 50mm)
        \\let c = line(a, b)
        \\
    ;
    try std.testing.expectEqualStrings(expected, output);
}

test "decompile roundtrip: line constructor" {
    try expectDecompileRoundtrip(
        \\let a = point(0mm, 0mm)
        \\let b = point(100mm, 50mm)
        \\let c = line(a, b)
    );
}

test "decompile roundtrip: line with expression args" {
    try expectDecompileRoundtrip(
        \\let a = point(0mm, 0mm)
        \\let b = point(100mm, 50mm)
        \\let c = line(a, b)
    );
}

test "decompile roundtrip: fn_def simple" {
    try expectDecompileRoundtrip("fn double(x: f64) { return x * 2 }");
}

test "decompile roundtrip: fn_def with body" {
    try expectDecompileRoundtrip(
        \\fn half(x: length) {
        \\  let result = x / 2
        \\  return result
        \\}
    );
}

test "decompile roundtrip: fn_def and call" {
    try expectDecompileRoundtrip(
        \\fn double(x: f64) { return x * 2 }
        \\let y = double(5)
    );
}

test "decompile roundtrip: fn with input ref and call" {
    try expectDecompileRoundtrip(
        \\input head = 100mm
        \\fn scale_head(factor: f64) { return head * factor }
        \\let y = scale_head(2)
    );
}

test "decompile roundtrip: fn returning literal" {
    try expectDecompileRoundtrip("fn zero() { return 42 }");
}

test "decompile roundtrip: fn multiple params" {
    try expectDecompileRoundtrip(
        \\fn add(a: length, b: length) { return a + b }
        \\input x = 10mm
        \\input y = 20mm
        \\let z = add(x, y)
    );
}
