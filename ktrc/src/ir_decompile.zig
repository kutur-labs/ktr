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
fn opToInfix(op: Op) []const u8 {
    return switch (op) {
        .add => " + ",
        .sub => " - ",
        .mul => " * ",
        .div => " / ",
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
                if (b.lhs == .ref) {
                    const entry = try counts.getOrPut(b.lhs.ref);
                    if (!entry.found_existing) entry.value_ptr.* = 0;
                    entry.value_ptr.* += 1;
                }
                if (b.rhs == .ref) {
                    const entry = try counts.getOrPut(b.rhs.ref);
                    if (!entry.found_existing) entry.value_ptr.* = 0;
                    entry.value_ptr.* += 1;
                }
            },
            .constant => {},
        }
    }
    return counts;
}

/// Check if a name looks like a compiler-generated temp (all digits).
fn isTempName(name: []const u8) bool {
    for (name) |c| {
        if (!std.ascii.isDigit(c)) return false;
    }
    return name.len > 0;
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
    return switch (op) {
        .add, .sub => 1,
        .mul, .div => 2,
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
        return isTempName(name) and (self.use_counts.get(name) orelse 0) == 1;
    }

    /// Write a bare literal value (number with optional unit suffix).
    fn writeLiteral(writer: anytype, v: Value) !void {
        try v.writeNumber(writer);
        if (v.unit) |u| try writer.writeAll(u.toStr());
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
                                const needs_parens = needsParentheses(b.op, parent_op, is_rhs);
                                if (needs_parens) try writer.writeByte('(');
                                try self.writeExpr(writer, b.lhs, b.op, false);
                                try writer.writeAll(opToInfix(b.op));
                                try self.writeExpr(writer, b.rhs, b.op, true);
                                if (needs_parens) try writer.writeByte(')');
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
                        }
                    }
                }
                try writer.writeAll(name);
            },
        }
    }
};

/// Reconstruct `.ktr` source from an `Ir`.
///
/// Instructions that are single-use compiler temporaries (numeric names used
/// exactly once) are inlined into their parent expression. All other
/// instructions emit a `let` binding.
pub fn decompile(allocator: std.mem.Allocator, ir_data: Ir, writer: anytype) !void {
    var dc = try Decompiler.init(allocator, ir_data.instructions);
    defer dc.deinit();

    var first = true;
    for (ir_data.instructions) |inst| {
        // Skip single-use temps -- they will be inlined.
        if (dc.isSingleUseTemp(inst.name)) continue;

        if (!first) try writer.writeByte('\n');
        first = false;

        try writer.print("let {s} = ", .{inst.name});

        switch (inst.rhs) {
            .constant => |v| try writeKtrValue(writer, v, inst.ty),
            .copy => |name| try writer.writeAll(name),
            .builtin => |b| {
                try dc.writeExpr(writer, b.lhs, b.op, false);
                try writer.writeAll(opToInfix(b.op));
                try dc.writeExpr(writer, b.rhs, b.op, true);
            },
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
    try decompile(allocator, ir1, buf.writer(allocator));
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
            .lhs = .{ .ref = try ally.dupe(u8, "a") },
            .rhs = .{ .literal = .{ .number = 2.0, .unit = null } },
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
            .lhs = .{ .literal = .{ .number = 2.0, .unit = null } },
            .rhs = .{ .literal = .{ .number = 2.0, .unit = null } },
        } },
    };
    insts[1] = .{
        .name = try ally.dupe(u8, "x"),
        .ty = .f64,
        .rhs = .{ .builtin = .{
            .op = .div,
            .lhs = .{ .ref = try ally.dupe(u8, "0") },
            .rhs = .{ .literal = .{ .number = 2.0, .unit = null } },
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

test "decompile roundtrip: arithmetic source -> lower -> decompile -> re-lower" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "let a = 100mm\nlet x = a * 2";

    var tree1 = try parser.parse(allocator, source);
    defer tree1.deinit();

    var sem1 = try sema.analyze(allocator, &tree1);
    defer sem1.deinit();

    var ir1 = try lower.lower(allocator, &tree1, &sem1);
    defer ir1.deinit();

    var buf = std.ArrayList(u8).empty;
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

test "decompile roundtrip: grouped expression" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "let x = (2 + 2) / 2";

    var tree1 = try parser.parse(allocator, source);
    defer tree1.deinit();

    var sem1 = try sema.analyze(allocator, &tree1);
    defer sem1.deinit();

    var ir1 = try lower.lower(allocator, &tree1, &sem1);
    defer ir1.deinit();

    var buf = std.ArrayList(u8).empty;
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
