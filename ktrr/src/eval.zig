const std = @import("std");
const Allocator = std.mem.Allocator;
const ktr_ir = @import("ktr_ir");
const Ir = ktr_ir.Ir;
const Inst = ktr_ir.Inst;
const Value = ktr_ir.Value;
const Type = ktr_ir.Type;
const Op = ktr_ir.Op;
const Operand = ktr_ir.Operand;
const LengthUnit = ktr_ir.LengthUnit;
const Input = ktr_ir.Input;

// ─── Public types ───────────────────────────────────────────────────────────

pub const InputOverride = struct {
    name: []const u8,
    value: f64, // already normalized to mm for lengths
};

/// A runtime value that can hold either a scalar or a structured type.
pub const RuntimeValue = union(enum) {
    /// Scalar value: used for f64, length (in mm), and percentage.
    scalar: f64,
    /// 2D point: [x, y] both in mm.
    point: [2]f64,
    /// Cubic Bezier curve: 4 control points, each [x, y] in mm.
    bezier: [4][2]f64,
    /// Straight line segment: [start, end], each [x, y] in mm.
    line: [2][2]f64,
    /// Piece value: named members with already-evaluated runtime values.
    piece: PieceValue,

    /// Extract the scalar payload. Asserts the value is a scalar.
    pub fn asScalar(self: RuntimeValue) f64 {
        return switch (self) {
            .scalar => |v| v,
            .point, .bezier, .line, .piece => unreachable,
        };
    }

    /// Extract the point payload. Asserts the value is a point.
    pub fn asPoint(self: RuntimeValue) [2]f64 {
        return switch (self) {
            .point => |p| p,
            .scalar, .bezier, .line, .piece => unreachable,
        };
    }

    /// Extract the line payload. Asserts the value is a line.
    pub fn asLine(self: RuntimeValue) [2][2]f64 {
        return switch (self) {
            .line => |l| l,
            .scalar, .point, .bezier, .piece => unreachable,
        };
    }

    /// Extract the bezier payload. Asserts the value is a bezier.
    pub fn asBezier(self: RuntimeValue) [4][2]f64 {
        return switch (self) {
            .bezier => |b| b,
            .scalar, .point, .line, .piece => unreachable,
        };
    }
};

pub const PieceMemberValue = struct {
    name: []const u8,
    value: RuntimeValue,
};

pub const PieceValue = struct {
    members: []const PieceMemberValue,

    fn get(self: PieceValue, name: []const u8) ?RuntimeValue {
        for (self.members) |member| {
            if (std.mem.eql(u8, member.name, name)) return member.value;
        }
        return null;
    }
};

pub const Binding = struct {
    name: []const u8,
    ty: Type,
    value: RuntimeValue,
    is_input: bool,
};

pub const Result = struct {
    bindings: []const Binding,
    arena: std.heap.ArenaAllocator,

    pub fn deinit(self: *Result) void {
        self.arena.deinit();
        self.* = undefined;
    }
};

pub const EvalError = error{
    UndefinedReference,
    DivisionByZero,
    UnsupportedOperation,
} || Allocator.Error;

// ─── Evaluator ──────────────────────────────────────────────────────────────

/// Look up an override value by name. Returns null if no override exists.
fn findOverride(overrides: []const InputOverride, name: []const u8) ?f64 {
    for (overrides) |ov| {
        if (std.mem.eql(u8, ov.name, name)) return ov.value;
    }
    return null;
}

/// Evaluate a parsed IR program and return all user-defined bindings with
/// their resolved values. Compiler temporaries (numeric names) are evaluated
/// but excluded from the result.
///
/// `overrides` provides runtime input overrides. For each input, if a
/// matching override exists, its value is used instead of the default.
/// Pass `&.{}` for no overrides.
///
/// The returned `Result` is self-contained; the caller may free the `Ir`
/// immediately after this function returns.
pub fn eval(gpa: Allocator, ir_data: Ir, overrides: []const InputOverride) EvalError!Result {
    var arena = std.heap.ArenaAllocator.init(gpa);
    errdefer arena.deinit();
    const ally = arena.allocator();

    // Pre-build function lookup map for O(1) calls.
    const fn_map = try buildFnMap(ally, ir_data.functions);

    // Working environment: maps binding name -> resolved RuntimeValue.
    var env = Env{};
    const scope = Scope{ .bindings = &env, .parent = null };

    // Collect user-visible bindings (skip compiler temps).
    var bindings = std.ArrayListUnmanaged(Binding){};

    // Process inputs first: apply overrides or use defaults.
    for (ir_data.inputs) |input| {
        const scalar = findOverride(overrides, input.name) orelse normalizeToMm(input.default);
        const value = RuntimeValue{ .scalar = scalar };
        try env.put(ally, input.name, value);
        try bindings.append(ally, .{
            .name = try ally.dupe(u8, input.name),
            .ty = input.ty,
            .value = value,
            .is_input = true,
        });
    }

    // Evaluate top-level piece blocks. Members are evaluated in a local scope
    // with lexical fallback to outer/global bindings, then exported under
    // qualified names (`piece.member`) and as a piece-typed binding.
    for (ir_data.pieces) |piece_def| {
        var piece_env = Env{};
        const piece_scope = Scope{ .bindings = &piece_env, .parent = &scope };
        var members = std.ArrayListUnmanaged(PieceMemberValue){};

        for (piece_def.members) |inst| {
            const value = try evalInst(ally, piece_scope, fn_map, inst);
            try piece_env.put(ally, inst.name, value);

            try members.append(ally, .{
                .name = try ally.dupe(u8, inst.name),
                .value = value,
            });

            const qualified_name = try std.fmt.allocPrint(ally, "{s}.{s}", .{ piece_def.name, inst.name });
            try env.put(ally, qualified_name, value);
            try appendUserBinding(&bindings, ally, qualified_name, inst.ty, value, false);
        }

        const piece_value = RuntimeValue{ .piece = .{
            .members = try members.toOwnedSlice(ally),
        } };
        try env.put(ally, piece_def.name, piece_value);
        try bindings.append(ally, .{
            .name = try ally.dupe(u8, piece_def.name),
            .ty = .piece,
            .value = piece_value,
            .is_input = false,
        });
    }

    // Process instructions.
    for (ir_data.instructions) |inst| {
        const value = try evalInst(ally, scope, fn_map, inst);
        try env.put(ally, inst.name, value);
        try appendUserBinding(&bindings, ally, inst.name, inst.ty, value, false);
    }

    return .{
        .bindings = try bindings.toOwnedSlice(ally),
        .arena = arena,
    };
}

// ─── Internal helpers ───────────────────────────────────────────────────────

/// Append a user-visible binding, skipping compiler temporaries.
fn appendUserBinding(bindings: *std.ArrayListUnmanaged(Binding), ally: Allocator, name: []const u8, ty: Type, value: RuntimeValue, is_input: bool) Allocator.Error!void {
    if (isTemp(name)) return;
    try bindings.append(ally, .{
        .name = try ally.dupe(u8, name),
        .ty = ty,
        .value = value,
        .is_input = is_input,
    });
}

const Env = std.StringHashMapUnmanaged(RuntimeValue);
const FnMap = std.StringHashMapUnmanaged(ktr_ir.FnDef);

/// A scope frame with optional parent link, forming a chain for nested
/// function calls. Lookups walk the chain until found or exhausted.
const Scope = struct {
    bindings: *const Env,
    parent: ?*const Scope,

    fn get(self: Scope, name: []const u8) ?RuntimeValue {
        if (self.bindings.get(name)) |v| return v;
        if (self.parent) |p| return p.get(name);
        return null;
    }
};

/// Build a lookup map from function name -> FnDef for O(1) call resolution.
fn buildFnMap(ally: Allocator, functions: []const ktr_ir.FnDef) Allocator.Error!FnMap {
    var map = FnMap{};
    for (functions) |f| {
        try map.put(ally, f.name, f);
    }
    return map;
}

/// Normalize a Value to millimeters. Bare numbers and percentages pass
/// through unchanged; lengths are converted to mm.
fn normalizeToMm(v: Value) f64 {
    const u = v.unit orelse return v.number;
    return switch (u) {
        .mm => v.number,
        .cm => v.number * 10.0,
    };
}

/// Resolve an operand to its RuntimeValue via the scope chain.
fn resolveOperand(scope: Scope, operand: Operand) EvalError!RuntimeValue {
    return switch (operand) {
        .ref => |name| scope.get(name) orelse return error.UndefinedReference,
        .literal => |v| .{ .scalar = normalizeToMm(v) },
    };
}

/// Resolve an operand that must be a scalar (f64/length/percentage).
fn resolveScalar(scope: Scope, operand: Operand) EvalError!f64 {
    const rv = try resolveOperand(scope, operand);
    return rv.asScalar();
}

/// Evaluate a builtin operation.
fn evalBuiltin(scope: Scope, b: Inst.Builtin) EvalError!RuntimeValue {
    return switch (b.op) {
        .add => .{ .scalar = try resolveScalar(scope, b.operands[0]) + try resolveScalar(scope, b.operands[1]) },
        .sub => .{ .scalar = try resolveScalar(scope, b.operands[0]) - try resolveScalar(scope, b.operands[1]) },
        .mul => .{ .scalar = try resolveScalar(scope, b.operands[0]) * try resolveScalar(scope, b.operands[1]) },
        .div => {
            const lhs = try resolveScalar(scope, b.operands[0]);
            const rhs = try resolveScalar(scope, b.operands[1]);
            if (rhs == 0.0) return error.DivisionByZero;
            return .{ .scalar = lhs / rhs };
        },
        .point => .{ .point = .{
            try resolveScalar(scope, b.operands[0]),
            try resolveScalar(scope, b.operands[1]),
        } },
        .bezier => .{ .bezier = .{
            (try resolveOperand(scope, b.operands[0])).asPoint(),
            (try resolveOperand(scope, b.operands[1])).asPoint(),
            (try resolveOperand(scope, b.operands[2])).asPoint(),
            (try resolveOperand(scope, b.operands[3])).asPoint(),
        } },
        .line => .{ .line = .{
            (try resolveOperand(scope, b.operands[0])).asPoint(),
            (try resolveOperand(scope, b.operands[1])).asPoint(),
        } },
        .point_x => .{ .scalar = (try resolveOperand(scope, b.operands[0])).asPoint()[0] },
        .point_y => .{ .scalar = (try resolveOperand(scope, b.operands[0])).asPoint()[1] },
        .line_p1 => .{ .point = (try resolveOperand(scope, b.operands[0])).asLine()[0] },
        .line_p2 => .{ .point = (try resolveOperand(scope, b.operands[0])).asLine()[1] },
        .bezier_p1 => .{ .point = (try resolveOperand(scope, b.operands[0])).asBezier()[0] },
        .bezier_p2 => .{ .point = (try resolveOperand(scope, b.operands[0])).asBezier()[1] },
        .bezier_p3 => .{ .point = (try resolveOperand(scope, b.operands[0])).asBezier()[2] },
        .bezier_p4 => .{ .point = (try resolveOperand(scope, b.operands[0])).asBezier()[3] },
        .piece_member => {
            if (b.operands.len != 2 or b.operands[1] != .ref) return error.UnsupportedOperation;
            const piece_value = try resolveOperand(scope, b.operands[0]);
            const member_name = b.operands[1].ref;
            return switch (piece_value) {
                .piece => |p| p.get(member_name) orelse error.UndefinedReference,
                else => error.UnsupportedOperation,
            };
        },
    };
}

/// Evaluate a single instruction RHS to a RuntimeValue.
fn evalInst(ally: Allocator, scope: Scope, fn_map: FnMap, inst: Inst) EvalError!RuntimeValue {
    return switch (inst.rhs) {
        .constant => |v| .{ .scalar = normalizeToMm(v) },
        .copy => |name| scope.get(name) orelse return error.UndefinedReference,
        .builtin => |b| try evalBuiltin(scope, b),
        .call => |c| try evalCall(ally, scope, fn_map, c),
    };
}

/// Evaluate a user-defined function call by inlining: bind params to args,
/// evaluate body instructions, return the `ret` value.
fn evalCall(
    ally: Allocator,
    caller_scope: Scope,
    fn_map: FnMap,
    c: Inst.Call,
) EvalError!RuntimeValue {
    const fn_def = fn_map.get(c.func) orelse return error.UndefinedReference;

    // Build a local environment with only params + body locals.
    var fn_env = Env{};

    for (fn_def.params, c.args) |param, arg| {
        try fn_env.put(ally, param.name, try resolveOperand(caller_scope, arg));
    }

    // The function body sees its own locals first, then the caller's
    // full scope chain (which includes inputs and outer bindings).
    const fn_scope = Scope{ .bindings = &fn_env, .parent = &caller_scope };

    // For piece-returning functions, collect members in a single pass.
    var maybe_members: ?std.ArrayListUnmanaged(PieceMemberValue) =
        if (fn_def.ret_ty == .piece) .{} else null;

    for (fn_def.body) |inst| {
        const value = try evalInst(ally, fn_scope, fn_map, inst);
        try fn_env.put(ally, inst.name, value);
        if (maybe_members) |*members| {
            if (!isTemp(inst.name)) {
                try members.append(ally, .{
                    .name = try ally.dupe(u8, inst.name),
                    .value = value,
                });
            }
        }
    }

    if (maybe_members) |*members| {
        return .{ .piece = .{
            .members = try members.toOwnedSlice(ally),
        } };
    }

    return fn_scope.get(fn_def.ret) orelse error.UndefinedReference;
}

/// Returns true if a binding name is a compiler-generated temporary.
const isTemp = ktr_ir.isTemp;

// ─── Tests ──────────────────────────────────────────────────────────────────

const parse = ktr_ir.parse;

fn evalSource(allocator: Allocator, source: []const u8) (EvalError || ktr_ir.ParseError)!Result {
    return evalSourceWithOverrides(allocator, source, &.{});
}

fn evalSourceWithOverrides(allocator: Allocator, source: []const u8, overrides: []const InputOverride) (EvalError || ktr_ir.ParseError)!Result {
    var ir_data = try parse(allocator, source);
    defer ir_data.deinit();
    return eval(allocator, ir_data, overrides);
}

/// Find a binding by name in results.
fn findBinding(bindings: []const Binding, name: []const u8) ?Binding {
    for (bindings) |b| {
        if (std.mem.eql(u8, b.name, name)) return b;
    }
    return null;
}

test "eval: constant length" {
    const ally = std.testing.allocator;
    var result = try evalSource(ally,
        \\# ktr-ir v1
        \\
        \\%x : length = 100mm
    );
    defer result.deinit();

    try std.testing.expectEqual(1, result.bindings.len);
    const b = result.bindings[0];
    try std.testing.expectEqualStrings("x", b.name);
    try std.testing.expectEqual(Type.length, b.ty);
    try std.testing.expectEqual(@as(f64, 100.0), b.value.asScalar());
}

test "eval: constant percentage" {
    const ally = std.testing.allocator;
    var result = try evalSource(ally,
        \\# ktr-ir v1
        \\
        \\%p : percentage = 50
    );
    defer result.deinit();

    const b = result.bindings[0];
    try std.testing.expectEqual(Type.percentage, b.ty);
    try std.testing.expectEqual(@as(f64, 50.0), b.value.asScalar());
}

test "eval: constant f64" {
    const ally = std.testing.allocator;
    var result = try evalSource(ally,
        \\# ktr-ir v1
        \\
        \\%c : f64 = 42.2
    );
    defer result.deinit();

    const b = result.bindings[0];
    try std.testing.expectEqual(Type.f64, b.ty);
    try std.testing.expectEqual(@as(f64, 42.2), b.value.asScalar());
}

test "eval: unit conversion cm to mm" {
    const ally = std.testing.allocator;
    var result = try evalSource(ally,
        \\# ktr-ir v1
        \\
        \\%x : length = 2cm
    );
    defer result.deinit();

    try std.testing.expectEqual(@as(f64, 20.0), result.bindings[0].value.asScalar());
}

test "eval: copy reference" {
    const ally = std.testing.allocator;
    var result = try evalSource(ally,
        \\# ktr-ir v1
        \\
        \\%x : length = 100mm
        \\%y : length = %x
    );
    defer result.deinit();

    try std.testing.expectEqual(2, result.bindings.len);
    try std.testing.expectEqual(@as(f64, 100.0), result.bindings[1].value.asScalar());
    try std.testing.expectEqualStrings("y", result.bindings[1].name);
}

test "eval: add two refs" {
    const ally = std.testing.allocator;
    var result = try evalSource(ally,
        \\# ktr-ir v1
        \\
        \\%a : f64 = 10
        \\%b : f64 = 20
        \\%c : f64 = add %a %b
    );
    defer result.deinit();

    const c = findBinding(result.bindings, "c").?;
    try std.testing.expectEqual(@as(f64, 30.0), c.value.asScalar());
}

test "eval: sub two literals" {
    const ally = std.testing.allocator;
    var result = try evalSource(ally,
        \\# ktr-ir v1
        \\
        \\%x : f64 = sub 10 3
    );
    defer result.deinit();

    try std.testing.expectEqual(@as(f64, 7.0), result.bindings[0].value.asScalar());
}

test "eval: mul ref and literal" {
    const ally = std.testing.allocator;
    var result = try evalSource(ally,
        \\# ktr-ir v1
        \\
        \\%a : length = 100mm
        \\%x : length = mul %a 2
    );
    defer result.deinit();

    const x = findBinding(result.bindings, "x").?;
    try std.testing.expectEqual(@as(f64, 200.0), x.value.asScalar());
    try std.testing.expectEqual(Type.length, x.ty);
}

test "eval: div two refs" {
    const ally = std.testing.allocator;
    var result = try evalSource(ally,
        \\# ktr-ir v1
        \\
        \\%a : f64 = 10
        \\%b : f64 = 4
        \\%x : f64 = div %a %b
    );
    defer result.deinit();

    try std.testing.expectEqual(@as(f64, 2.5), findBinding(result.bindings, "x").?.value.asScalar());
}

test "eval: mixed-unit add (mm + cm)" {
    const ally = std.testing.allocator;
    var result = try evalSource(ally,
        \\# ktr-ir v1
        \\
        \\%x : length = add 100mm 2cm
    );
    defer result.deinit();

    // 100mm + 2cm = 100 + 20 = 120mm
    try std.testing.expectEqual(@as(f64, 120.0), result.bindings[0].value.asScalar());
}

test "eval: division by zero" {
    const ally = std.testing.allocator;
    const result = evalSource(ally,
        \\# ktr-ir v1
        \\
        \\%x : f64 = div 10 0
    );
    try std.testing.expectError(error.DivisionByZero, result);
}

test "eval: undefined reference" {
    const ally = std.testing.allocator;
    const result = evalSource(ally,
        \\# ktr-ir v1
        \\
        \\%x : length = %nope
    );
    try std.testing.expectError(error.UndefinedReference, result);
}

test "eval: temp bindings excluded from results" {
    const ally = std.testing.allocator;
    var result = try evalSource(ally,
        \\# ktr-ir v1
        \\
        \\%a : f64 = 2
        \\%0 : f64 = add %a 3
        \\%x : f64 = mul %0 4
    );
    defer result.deinit();

    // %0 is a temp -- should not appear in results.
    try std.testing.expectEqual(2, result.bindings.len);
    try std.testing.expectEqualStrings("a", result.bindings[0].name);
    try std.testing.expectEqualStrings("x", result.bindings[1].name);
    // (2 + 3) * 4 = 20
    try std.testing.expectEqual(@as(f64, 20.0), result.bindings[1].value.asScalar());
}

test "eval: full user example" {
    const ally = std.testing.allocator;

    // The reference program from the spec:
    //   let a = 100mm
    //   let b = 50%
    //   let c = 42.2
    //   let d = a * c
    //   let e = (a + 20mm) * c
    //
    // Lowered IR:
    var result = try evalSource(ally,
        \\# ktr-ir v1
        \\
        \\%a : length = 100mm
        \\%b : percentage = 50
        \\%c : f64 = 42.2
        \\%d : length = mul %a %c
        \\%1 : length = add %a 20mm
        \\%e : length = mul %1 %c
    );
    defer result.deinit();

    // 5 user bindings (a, b, c, d, e); %1 is excluded.
    try std.testing.expectEqual(5, result.bindings.len);

    const a = findBinding(result.bindings, "a").?;
    try std.testing.expectEqual(Type.length, a.ty);
    try std.testing.expectEqual(@as(f64, 100.0), a.value.asScalar());

    const b = findBinding(result.bindings, "b").?;
    try std.testing.expectEqual(Type.percentage, b.ty);
    try std.testing.expectEqual(@as(f64, 50.0), b.value.asScalar());

    const c = findBinding(result.bindings, "c").?;
    try std.testing.expectEqual(Type.f64, c.ty);
    try std.testing.expectEqual(@as(f64, 42.2), c.value.asScalar());

    const d = findBinding(result.bindings, "d").?;
    try std.testing.expectEqual(Type.length, d.ty);
    // 100 * 42.2 = 4220
    try std.testing.expectEqual(@as(f64, 4220.0), d.value.asScalar());

    const e = findBinding(result.bindings, "e").?;
    try std.testing.expectEqual(Type.length, e.ty);
    // (100 + 20) * 42.2 = 120 * 42.2 = 5064
    try std.testing.expectEqual(@as(f64, 5064.0), e.value.asScalar());
}

test "eval: input with default value" {
    const ally = std.testing.allocator;
    var result = try evalSource(ally,
        \\# ktr-ir v1
        \\
        \\input %head : length = 100mm
    );
    defer result.deinit();

    try std.testing.expectEqual(1, result.bindings.len);
    const b = result.bindings[0];
    try std.testing.expectEqualStrings("head", b.name);
    try std.testing.expectEqual(Type.length, b.ty);
    try std.testing.expectEqual(@as(f64, 100.0), b.value.asScalar());
    try std.testing.expect(b.is_input);
}

test "eval: input referenced in instruction" {
    const ally = std.testing.allocator;
    var result = try evalSource(ally,
        \\# ktr-ir v1
        \\
        \\input %head : length = 100mm
        \\
        \\%x : length = mul %head 2
    );
    defer result.deinit();

    try std.testing.expectEqual(2, result.bindings.len);

    const head = findBinding(result.bindings, "head").?;
    try std.testing.expectEqual(@as(f64, 100.0), head.value.asScalar());
    try std.testing.expect(head.is_input);

    const x = findBinding(result.bindings, "x").?;
    try std.testing.expectEqual(@as(f64, 200.0), x.value.asScalar());
    try std.testing.expect(!x.is_input);
}

test "eval: input override replaces default" {
    const ally = std.testing.allocator;
    var result = try evalSourceWithOverrides(ally,
        \\# ktr-ir v1
        \\
        \\input %head : length = 100mm
    , &.{.{ .name = "head", .value = 120.0 }});
    defer result.deinit();

    try std.testing.expectEqual(1, result.bindings.len);
    try std.testing.expectEqual(@as(f64, 120.0), result.bindings[0].value.asScalar());
    try std.testing.expect(result.bindings[0].is_input);
}

test "eval: override propagates to downstream instructions" {
    const ally = std.testing.allocator;
    var result = try evalSourceWithOverrides(ally,
        \\# ktr-ir v1
        \\
        \\input %head : length = 100mm
        \\
        \\%x : length = mul %head 2
    , &.{.{ .name = "head", .value = 150.0 }});
    defer result.deinit();

    const head = findBinding(result.bindings, "head").?;
    try std.testing.expectEqual(@as(f64, 150.0), head.value.asScalar());

    const x = findBinding(result.bindings, "x").?;
    // 150 * 2 = 300
    try std.testing.expectEqual(@as(f64, 300.0), x.value.asScalar());
}

test "eval: unknown override is ignored" {
    const ally = std.testing.allocator;
    var result = try evalSourceWithOverrides(ally,
        \\# ktr-ir v1
        \\
        \\input %head : length = 100mm
    , &.{.{ .name = "nonexistent", .value = 999.0 }});
    defer result.deinit();

    // Override for unknown name is ignored; default is used.
    try std.testing.expectEqual(@as(f64, 100.0), result.bindings[0].value.asScalar());
}

test "eval: multiple inputs with overrides" {
    const ally = std.testing.allocator;
    var result = try evalSourceWithOverrides(ally,
        \\# ktr-ir v1
        \\
        \\input %head : length = 100mm
        \\input %chest : length = 900mm
        \\
        \\%sum : length = add %head %chest
    , &.{.{ .name = "chest", .value = 1000.0 }});
    defer result.deinit();

    const head = findBinding(result.bindings, "head").?;
    try std.testing.expectEqual(@as(f64, 100.0), head.value.asScalar()); // default

    const chest = findBinding(result.bindings, "chest").?;
    try std.testing.expectEqual(@as(f64, 1000.0), chest.value.asScalar()); // overridden

    const sum = findBinding(result.bindings, "sum").?;
    try std.testing.expectEqual(@as(f64, 1100.0), sum.value.asScalar()); // 100 + 1000
}

test "eval: let bindings have is_input false" {
    const ally = std.testing.allocator;
    var result = try evalSource(ally,
        \\# ktr-ir v1
        \\
        \\%x : f64 = 42
    );
    defer result.deinit();

    try std.testing.expect(!result.bindings[0].is_input);
}

test "eval: input cm unit normalized" {
    const ally = std.testing.allocator;
    var result = try evalSource(ally,
        \\# ktr-ir v1
        \\
        \\input %w : length = 2cm
    );
    defer result.deinit();

    try std.testing.expectEqual(@as(f64, 20.0), result.bindings[0].value.asScalar());
    try std.testing.expect(result.bindings[0].is_input);
}

test "eval: point constructor" {
    const ally = std.testing.allocator;
    var result = try evalSource(ally,
        \\# ktr-ir v1
        \\
        \\%p : point = point 100mm 50mm
    );
    defer result.deinit();

    try std.testing.expectEqual(1, result.bindings.len);
    const b = result.bindings[0];
    try std.testing.expectEqualStrings("p", b.name);
    try std.testing.expectEqual(Type.point, b.ty);
    try std.testing.expectEqual(@as(f64, 100.0), b.value.point[0]);
    try std.testing.expectEqual(@as(f64, 50.0), b.value.point[1]);
}

test "eval: point with ref args" {
    const ally = std.testing.allocator;
    var result = try evalSource(ally,
        \\# ktr-ir v1
        \\
        \\input %head : length = 100mm
        \\
        \\%p : point = point %head 0mm
    );
    defer result.deinit();

    const p = findBinding(result.bindings, "p").?;
    try std.testing.expectEqual(Type.point, p.ty);
    try std.testing.expectEqual(@as(f64, 100.0), p.value.point[0]);
    try std.testing.expectEqual(@as(f64, 0.0), p.value.point[1]);
}

test "eval: point with cm normalization" {
    const ally = std.testing.allocator;
    var result = try evalSource(ally,
        \\# ktr-ir v1
        \\
        \\%p : point = point 2cm 3cm
    );
    defer result.deinit();

    const b = result.bindings[0];
    try std.testing.expectEqual(@as(f64, 20.0), b.value.point[0]);
    try std.testing.expectEqual(@as(f64, 30.0), b.value.point[1]);
}

test "eval: point copy" {
    const ally = std.testing.allocator;
    var result = try evalSource(ally,
        \\# ktr-ir v1
        \\
        \\%p : point = point 100mm 50mm
        \\%q : point = %p
    );
    defer result.deinit();

    const q = findBinding(result.bindings, "q").?;
    try std.testing.expectEqual(Type.point, q.ty);
    try std.testing.expectEqual(@as(f64, 100.0), q.value.point[0]);
    try std.testing.expectEqual(@as(f64, 50.0), q.value.point[1]);
}

test "eval: bezier constructor" {
    const ally = std.testing.allocator;
    var result = try evalSource(ally,
        \\# ktr-ir v1
        \\
        \\%p1 : point = point 0mm 0mm
        \\%p2 : point = point 100mm 0mm
        \\%p3 : point = point 100mm 100mm
        \\%p4 : point = point 0mm 100mm
        \\%c : bezier = bezier %p1 %p2 %p3 %p4
    );
    defer result.deinit();

    const c = findBinding(result.bindings, "c").?;
    try std.testing.expectEqual(Type.bezier, c.ty);
    try std.testing.expectEqual(@as(f64, 0.0), c.value.bezier[0][0]);
    try std.testing.expectEqual(@as(f64, 0.0), c.value.bezier[0][1]);
    try std.testing.expectEqual(@as(f64, 100.0), c.value.bezier[1][0]);
    try std.testing.expectEqual(@as(f64, 0.0), c.value.bezier[1][1]);
    try std.testing.expectEqual(@as(f64, 100.0), c.value.bezier[2][0]);
    try std.testing.expectEqual(@as(f64, 100.0), c.value.bezier[2][1]);
    try std.testing.expectEqual(@as(f64, 0.0), c.value.bezier[3][0]);
    try std.testing.expectEqual(@as(f64, 100.0), c.value.bezier[3][1]);
}

test "eval: bezier with ref args" {
    const ally = std.testing.allocator;
    var result = try evalSource(ally,
        \\# ktr-ir v1
        \\
        \\input %head : length = 100mm
        \\
        \\%p1 : point = point %head 0mm
        \\%p2 : point = point 0mm %head
        \\%c : bezier = bezier %p1 %p2 %p1 %p2
    );
    defer result.deinit();

    const c = findBinding(result.bindings, "c").?;
    try std.testing.expectEqual(Type.bezier, c.ty);
    try std.testing.expectEqual(@as(f64, 100.0), c.value.bezier[0][0]);
    try std.testing.expectEqual(@as(f64, 0.0), c.value.bezier[0][1]);
    try std.testing.expectEqual(@as(f64, 0.0), c.value.bezier[1][0]);
    try std.testing.expectEqual(@as(f64, 100.0), c.value.bezier[1][1]);
}

test "eval: bezier copy" {
    const ally = std.testing.allocator;
    var result = try evalSource(ally,
        \\# ktr-ir v1
        \\
        \\%p1 : point = point 0mm 0mm
        \\%p2 : point = point 100mm 100mm
        \\%c : bezier = bezier %p1 %p2 %p1 %p2
        \\%d : bezier = %c
    );
    defer result.deinit();

    const d = findBinding(result.bindings, "d").?;
    try std.testing.expectEqual(Type.bezier, d.ty);
    try std.testing.expectEqual(@as(f64, 0.0), d.value.bezier[0][0]);
    try std.testing.expectEqual(@as(f64, 100.0), d.value.bezier[1][0]);
}

test "eval: line constructor" {
    const ally = std.testing.allocator;
    var result = try evalSource(ally,
        \\# ktr-ir v1
        \\
        \\%a : point = point 0mm 0mm
        \\%b : point = point 100mm 50mm
        \\%c : line = line %a %b
    );
    defer result.deinit();

    const c = findBinding(result.bindings, "c").?;
    try std.testing.expectEqual(Type.line, c.ty);
    try std.testing.expectEqual(@as(f64, 0.0), c.value.line[0][0]);
    try std.testing.expectEqual(@as(f64, 0.0), c.value.line[0][1]);
    try std.testing.expectEqual(@as(f64, 100.0), c.value.line[1][0]);
    try std.testing.expectEqual(@as(f64, 50.0), c.value.line[1][1]);
}

test "eval: line with ref args" {
    const ally = std.testing.allocator;
    var result = try evalSource(ally,
        \\# ktr-ir v1
        \\
        \\input %head : length = 100mm
        \\
        \\%p1 : point = point %head 0mm
        \\%p2 : point = point 0mm %head
        \\%c : line = line %p1 %p2
    );
    defer result.deinit();

    const c = findBinding(result.bindings, "c").?;
    try std.testing.expectEqual(Type.line, c.ty);
    try std.testing.expectEqual(@as(f64, 100.0), c.value.line[0][0]);
    try std.testing.expectEqual(@as(f64, 0.0), c.value.line[0][1]);
    try std.testing.expectEqual(@as(f64, 0.0), c.value.line[1][0]);
    try std.testing.expectEqual(@as(f64, 100.0), c.value.line[1][1]);
}

test "eval: line copy" {
    const ally = std.testing.allocator;
    var result = try evalSource(ally,
        \\# ktr-ir v1
        \\
        \\%a : point = point 0mm 0mm
        \\%b : point = point 100mm 50mm
        \\%c : line = line %a %b
        \\%d : line = %c
    );
    defer result.deinit();

    const d = findBinding(result.bindings, "d").?;
    try std.testing.expectEqual(Type.line, d.ty);
    try std.testing.expectEqual(@as(f64, 0.0), d.value.line[0][0]);
    try std.testing.expectEqual(@as(f64, 100.0), d.value.line[1][0]);
    try std.testing.expectEqual(@as(f64, 50.0), d.value.line[1][1]);
}

test "eval: line with cm normalization" {
    const ally = std.testing.allocator;
    var result = try evalSource(ally,
        \\# ktr-ir v1
        \\
        \\%a : point = point 2cm 3cm
        \\%b : point = point 5cm 1cm
        \\%c : line = line %a %b
    );
    defer result.deinit();

    const c = findBinding(result.bindings, "c").?;
    try std.testing.expectEqual(Type.line, c.ty);
    try std.testing.expectEqual(@as(f64, 20.0), c.value.line[0][0]);
    try std.testing.expectEqual(@as(f64, 30.0), c.value.line[0][1]);
    try std.testing.expectEqual(@as(f64, 50.0), c.value.line[1][0]);
    try std.testing.expectEqual(@as(f64, 10.0), c.value.line[1][1]);
}

test "eval: fn call simple" {
    const ally = std.testing.allocator;
    var result = try evalSource(ally,
        \\# ktr-ir v1
        \\
        \\fn double(%x : f64) -> f64
        \\  %0 : f64 = mul %x 2
        \\  ret %0
        \\end
        \\
        \\%y : f64 = call double 5
    );
    defer result.deinit();

    const y = findBinding(result.bindings, "y").?;
    try std.testing.expectEqual(Type.f64, y.ty);
    try std.testing.expectEqual(@as(f64, 10.0), y.value.asScalar());
}

test "eval: fn call with body" {
    const ally = std.testing.allocator;
    var result = try evalSource(ally,
        \\# ktr-ir v1
        \\
        \\fn half(%x : length) -> length
        \\  %result : length = div %x 2
        \\  ret %result
        \\end
        \\
        \\%y : length = call half 100mm
    );
    defer result.deinit();

    const y = findBinding(result.bindings, "y").?;
    try std.testing.expectEqual(Type.length, y.ty);
    try std.testing.expectEqual(@as(f64, 50.0), y.value.asScalar());
}

test "eval: fn call with input ref" {
    const ally = std.testing.allocator;
    var result = try evalSource(ally,
        \\# ktr-ir v1
        \\
        \\input %head : length = 100mm
        \\
        \\fn scale_head(%factor : f64) -> length
        \\  %0 : length = mul %head %factor
        \\  ret %0
        \\end
        \\
        \\%y : length = call scale_head 2
    );
    defer result.deinit();

    const y = findBinding(result.bindings, "y").?;
    try std.testing.expectEqual(@as(f64, 200.0), y.value.asScalar());
}

test "eval: fn call with input override" {
    const ally = std.testing.allocator;
    var result = try evalSourceWithOverrides(ally,
        \\# ktr-ir v1
        \\
        \\input %head : length = 100mm
        \\
        \\fn scale_head(%factor : f64) -> length
        \\  %0 : length = mul %head %factor
        \\  ret %0
        \\end
        \\
        \\%y : length = call scale_head 2
    , &.{.{ .name = "head", .value = 150.0 }});
    defer result.deinit();

    const y = findBinding(result.bindings, "y").?;
    try std.testing.expectEqual(@as(f64, 300.0), y.value.asScalar());
}

test "eval: fn call with ref arg" {
    const ally = std.testing.allocator;
    var result = try evalSource(ally,
        \\# ktr-ir v1
        \\
        \\fn double(%x : f64) -> f64
        \\  %0 : f64 = mul %x 2
        \\  ret %0
        \\end
        \\
        \\%a : f64 = 5
        \\%y : f64 = call double %a
    );
    defer result.deinit();

    const y = findBinding(result.bindings, "y").?;
    try std.testing.expectEqual(@as(f64, 10.0), y.value.asScalar());
}

test "eval: fn call multiple params" {
    const ally = std.testing.allocator;
    var result = try evalSource(ally,
        \\# ktr-ir v1
        \\
        \\fn add(%a : length, %b : length) -> length
        \\  %0 : length = add %a %b
        \\  ret %0
        \\end
        \\
        \\%z : length = call add 10mm 20mm
    );
    defer result.deinit();

    const z = findBinding(result.bindings, "z").?;
    try std.testing.expectEqual(@as(f64, 30.0), z.value.asScalar());
}

test "eval: fn call no params" {
    const ally = std.testing.allocator;
    var result = try evalSource(ally,
        \\# ktr-ir v1
        \\
        \\fn zero() -> f64
        \\  %0 : f64 = 42
        \\  ret %0
        \\end
        \\
        \\%y : f64 = call zero
    );
    defer result.deinit();

    const y = findBinding(result.bindings, "y").?;
    try std.testing.expectEqual(@as(f64, 42.0), y.value.asScalar());
}

test "eval: fn returning point" {
    const ally = std.testing.allocator;
    var result = try evalSource(ally,
        \\# ktr-ir v1
        \\
        \\fn origin() -> point
        \\  %0 : point = point 0mm 0mm
        \\  ret %0
        \\end
        \\
        \\%p : point = call origin
    );
    defer result.deinit();

    const p = findBinding(result.bindings, "p").?;
    try std.testing.expectEqual(Type.point, p.ty);
    try std.testing.expectEqual(@as(f64, 0.0), p.value.point[0]);
    try std.testing.expectEqual(@as(f64, 0.0), p.value.point[1]);
}

test "eval: plan key roundtrip test case" {
    const ally = std.testing.allocator;
    // The test case from the plan:
    // input head = 100mm
    // fn half_head(scale: f64) {
    //   let result = head * scale / 2
    //   return result
    // }
    // let x = half_head(1.0)
    //
    // Expected IR:
    var result = try evalSource(ally,
        \\# ktr-ir v1
        \\
        \\input %head : length = 100mm
        \\
        \\fn half_head(%scale : f64) -> length
        \\  %0 : length = mul %head %scale
        \\  %result : length = div %0 2
        \\  ret %result
        \\end
        \\
        \\%x : length = call half_head 1
    );
    defer result.deinit();

    const x = findBinding(result.bindings, "x").?;
    try std.testing.expectEqual(Type.length, x.ty);
    // (100 * 1.0) / 2 = 50.0
    try std.testing.expectEqual(@as(f64, 50.0), x.value.asScalar());
}

test "eval: point_x accessor" {
    const ally = std.testing.allocator;
    var result = try evalSource(ally,
        \\# ktr-ir v1
        \\
        \\%p : point = point 100mm 50mm
        \\%x : length = point_x %p
    );
    defer result.deinit();

    const px = findBinding(result.bindings, "x").?;
    try std.testing.expectEqual(Type.length, px.ty);
    try std.testing.expectEqual(@as(f64, 100.0), px.value.asScalar());
}

test "eval: point_y accessor" {
    const ally = std.testing.allocator;
    var result = try evalSource(ally,
        \\# ktr-ir v1
        \\
        \\%p : point = point 100mm 50mm
        \\%y : length = point_y %p
    );
    defer result.deinit();

    const py = findBinding(result.bindings, "y").?;
    try std.testing.expectEqual(Type.length, py.ty);
    try std.testing.expectEqual(@as(f64, 50.0), py.value.asScalar());
}

test "eval: line_p1 accessor" {
    const ally = std.testing.allocator;
    var result = try evalSource(ally,
        \\# ktr-ir v1
        \\
        \\%a : point = point 10mm 20mm
        \\%b : point = point 30mm 40mm
        \\%l : line = line %a %b
        \\%p : point = line_p1 %l
    );
    defer result.deinit();

    const p = findBinding(result.bindings, "p").?;
    try std.testing.expectEqual(Type.point, p.ty);
    try std.testing.expectEqual(@as(f64, 10.0), p.value.point[0]);
    try std.testing.expectEqual(@as(f64, 20.0), p.value.point[1]);
}

test "eval: line_p2 accessor" {
    const ally = std.testing.allocator;
    var result = try evalSource(ally,
        \\# ktr-ir v1
        \\
        \\%a : point = point 10mm 20mm
        \\%b : point = point 30mm 40mm
        \\%l : line = line %a %b
        \\%p : point = line_p2 %l
    );
    defer result.deinit();

    const p = findBinding(result.bindings, "p").?;
    try std.testing.expectEqual(Type.point, p.ty);
    try std.testing.expectEqual(@as(f64, 30.0), p.value.point[0]);
    try std.testing.expectEqual(@as(f64, 40.0), p.value.point[1]);
}

test "eval: bezier_p1 accessor" {
    const ally = std.testing.allocator;
    var result = try evalSource(ally,
        \\# ktr-ir v1
        \\
        \\%p1 : point = point 0mm 0mm
        \\%p2 : point = point 100mm 0mm
        \\%p3 : point = point 100mm 100mm
        \\%p4 : point = point 0mm 100mm
        \\%c : bezier = bezier %p1 %p2 %p3 %p4
        \\%q : point = bezier_p1 %c
    );
    defer result.deinit();

    const q = findBinding(result.bindings, "q").?;
    try std.testing.expectEqual(Type.point, q.ty);
    try std.testing.expectEqual(@as(f64, 0.0), q.value.point[0]);
    try std.testing.expectEqual(@as(f64, 0.0), q.value.point[1]);
}

test "eval: bezier_p3 accessor" {
    const ally = std.testing.allocator;
    var result = try evalSource(ally,
        \\# ktr-ir v1
        \\
        \\%p1 : point = point 0mm 0mm
        \\%p2 : point = point 100mm 0mm
        \\%p3 : point = point 100mm 100mm
        \\%p4 : point = point 0mm 100mm
        \\%c : bezier = bezier %p1 %p2 %p3 %p4
        \\%q : point = bezier_p3 %c
    );
    defer result.deinit();

    const q = findBinding(result.bindings, "q").?;
    try std.testing.expectEqual(Type.point, q.ty);
    try std.testing.expectEqual(@as(f64, 100.0), q.value.point[0]);
    try std.testing.expectEqual(@as(f64, 100.0), q.value.point[1]);
}

test "eval: chained line_p1 then point_x" {
    const ally = std.testing.allocator;
    var result = try evalSource(ally,
        \\# ktr-ir v1
        \\
        \\%a : point = point 10mm 20mm
        \\%b : point = point 30mm 40mm
        \\%l : line = line %a %b
        \\%0 : point = line_p1 %l
        \\%x : length = point_x %0
    );
    defer result.deinit();

    const x = findBinding(result.bindings, "x").?;
    try std.testing.expectEqual(Type.length, x.ty);
    try std.testing.expectEqual(@as(f64, 10.0), x.value.asScalar());
}

test "eval: accessor with arithmetic" {
    const ally = std.testing.allocator;
    var result = try evalSource(ally,
        \\# ktr-ir v1
        \\
        \\%p : point = point 100mm 50mm
        \\%px : length = point_x %p
        \\%x : length = mul %px 2
    );
    defer result.deinit();

    const x = findBinding(result.bindings, "x").?;
    try std.testing.expectEqual(Type.length, x.ty);
    try std.testing.expectEqual(@as(f64, 200.0), x.value.asScalar());
}

test "eval: top-level piece exports qualified members" {
    const ally = std.testing.allocator;
    var result = try evalSource(ally,
        \\# ktr-ir v1
        \\
        \\input %chest : length = 900mm
        \\
        \\piece neckhole
        \\  %top_left : point = point %chest 0mm
        \\  %x : length = point_x %top_left
        \\end
        \\
        \\%out : length = point_x %neckhole.top_left
    );
    defer result.deinit();

    const qualified_member = findBinding(result.bindings, "neckhole.top_left").?;
    try std.testing.expectEqual(Type.point, qualified_member.ty);
    try std.testing.expectEqual(@as(f64, 900.0), qualified_member.value.asPoint()[0]);
    try std.testing.expectEqual(@as(f64, 0.0), qualified_member.value.asPoint()[1]);

    const piece_binding = findBinding(result.bindings, "neckhole").?;
    try std.testing.expectEqual(Type.piece, piece_binding.ty);
    try std.testing.expectEqual(@as(usize, 2), piece_binding.value.piece.members.len);

    const out = findBinding(result.bindings, "out").?;
    try std.testing.expectEqual(Type.length, out.ty);
    try std.testing.expectEqual(@as(f64, 900.0), out.value.asScalar());
}

test "eval: piece-returning function and piece_member access" {
    const ally = std.testing.allocator;
    var result = try evalSource(ally,
        \\# ktr-ir v1
        \\
        \\fn make_piece(%w : length) -> piece
        \\  %top_left : point = point %w 50mm
        \\end
        \\
        \\%sleeve : piece = call make_piece 120mm
        \\%p : point = piece_member %sleeve %top_left
        \\%x : length = point_x %p
    );
    defer result.deinit();

    const sleeve = findBinding(result.bindings, "sleeve").?;
    try std.testing.expectEqual(Type.piece, sleeve.ty);
    try std.testing.expectEqual(@as(usize, 1), sleeve.value.piece.members.len);

    const p = findBinding(result.bindings, "p").?;
    try std.testing.expectEqual(Type.point, p.ty);
    try std.testing.expectEqual(@as(f64, 120.0), p.value.asPoint()[0]);
    try std.testing.expectEqual(@as(f64, 50.0), p.value.asPoint()[1]);

    const x = findBinding(result.bindings, "x").?;
    try std.testing.expectEqual(@as(f64, 120.0), x.value.asScalar());
}

test "eval: piece-returning function captures caller scope" {
    const ally = std.testing.allocator;
    var result = try evalSource(ally,
        \\# ktr-ir v1
        \\
        \\input %offset : length = 20mm
        \\
        \\fn make_piece(%w : length) -> piece
        \\  %0 : length = add %w %offset
        \\  %top_left : point = point %0 0mm
        \\end
        \\
        \\%piece : piece = call make_piece 80mm
        \\%p : point = piece_member %piece %top_left
        \\%x : length = point_x %p
    );
    defer result.deinit();

    const x = findBinding(result.bindings, "x").?;
    try std.testing.expectEqual(Type.length, x.ty);
    try std.testing.expectEqual(@as(f64, 100.0), x.value.asScalar());
}

test "eval: piece_member missing field" {
    const ally = std.testing.allocator;
    const result = evalSource(ally,
        \\# ktr-ir v1
        \\
        \\fn make_piece() -> piece
        \\  %top_left : point = point 0mm 0mm
        \\end
        \\
        \\%sleeve : piece = call make_piece
        \\%p : point = piece_member %sleeve %missing
    );
    try std.testing.expectError(error.UndefinedReference, result);
}

test "eval: piece_member on non-piece value is unsupported" {
    const ally = std.testing.allocator;
    const result = evalSource(ally,
        \\# ktr-ir v1
        \\
        \\%x : length = 10mm
        \\%p : point = piece_member %x %top_left
    );
    try std.testing.expectError(error.UnsupportedOperation, result);
}
