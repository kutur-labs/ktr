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

pub const Binding = struct {
    name: []const u8,
    ty: Type,
    value: f64, // normalized: lengths in mm
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

    // Working environment: maps binding name -> resolved f64.
    var env = std.StringHashMapUnmanaged(f64){};

    // Collect user-visible bindings (skip compiler temps).
    var bindings = std.ArrayListUnmanaged(Binding){};

    // Process inputs first: apply overrides or use defaults.
    for (ir_data.inputs) |input| {
        const value = findOverride(overrides, input.name) orelse normalizeToMm(input.default);
        try env.put(ally, input.name, value);
        try bindings.append(ally, .{
            .name = try ally.dupe(u8, input.name),
            .ty = input.ty,
            .value = value,
            .is_input = true,
        });
    }

    // Process instructions.
    for (ir_data.instructions) |inst| {
        const value = switch (inst.rhs) {
            .constant => |v| normalizeToMm(v),
            .copy => |name| env.get(name) orelse return error.UndefinedReference,
            .builtin => |b| try evalBuiltin(&env, b),
        };

        try env.put(ally, inst.name, value);

        // Only include user-defined bindings (names starting with a letter).
        if (!isTemp(inst.name)) {
            try bindings.append(ally, .{
                .name = try ally.dupe(u8, inst.name),
                .ty = inst.ty,
                .value = value,
                .is_input = false,
            });
        }
    }

    return .{
        .bindings = try bindings.toOwnedSlice(ally),
        .arena = arena,
    };
}

// ─── Internal helpers ───────────────────────────────────────────────────────

/// Normalize a Value to millimeters. Bare numbers and percentages pass
/// through unchanged; lengths are converted to mm.
fn normalizeToMm(v: Value) f64 {
    const u = v.unit orelse return v.number;
    return switch (u) {
        .mm => v.number,
        .cm => v.number * 10.0,
    };
}

/// Resolve an operand to its f64 value.
fn resolveOperand(env: *const std.StringHashMapUnmanaged(f64), operand: Operand) EvalError!f64 {
    return switch (operand) {
        .ref => |name| env.get(name) orelse return error.UndefinedReference,
        .literal => |v| normalizeToMm(v),
    };
}

/// Evaluate a builtin operation (add, sub, mul, div).
fn evalBuiltin(env: *const std.StringHashMapUnmanaged(f64), b: Inst.Builtin) EvalError!f64 {
    const lhs = try resolveOperand(env, b.lhs);
    const rhs = try resolveOperand(env, b.rhs);

    return switch (b.op) {
        .add => lhs + rhs,
        .sub => lhs - rhs,
        .mul => lhs * rhs,
        .div => {
            if (rhs == 0.0) return error.DivisionByZero;
            return lhs / rhs;
        },
    };
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
    try std.testing.expectEqual(@as(f64, 100.0), b.value);
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
    try std.testing.expectEqual(@as(f64, 50.0), b.value);
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
    try std.testing.expectEqual(@as(f64, 42.2), b.value);
}

test "eval: unit conversion cm to mm" {
    const ally = std.testing.allocator;
    var result = try evalSource(ally,
        \\# ktr-ir v1
        \\
        \\%x : length = 2cm
    );
    defer result.deinit();

    try std.testing.expectEqual(@as(f64, 20.0), result.bindings[0].value);
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
    try std.testing.expectEqual(@as(f64, 100.0), result.bindings[1].value);
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
    try std.testing.expectEqual(@as(f64, 30.0), c.value);
}

test "eval: sub two literals" {
    const ally = std.testing.allocator;
    var result = try evalSource(ally,
        \\# ktr-ir v1
        \\
        \\%x : f64 = sub 10 3
    );
    defer result.deinit();

    try std.testing.expectEqual(@as(f64, 7.0), result.bindings[0].value);
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
    try std.testing.expectEqual(@as(f64, 200.0), x.value);
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

    try std.testing.expectEqual(@as(f64, 2.5), findBinding(result.bindings, "x").?.value);
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
    try std.testing.expectEqual(@as(f64, 120.0), result.bindings[0].value);
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
    try std.testing.expectEqual(@as(f64, 20.0), result.bindings[1].value);
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
    try std.testing.expectEqual(@as(f64, 100.0), a.value);

    const b = findBinding(result.bindings, "b").?;
    try std.testing.expectEqual(Type.percentage, b.ty);
    try std.testing.expectEqual(@as(f64, 50.0), b.value);

    const c = findBinding(result.bindings, "c").?;
    try std.testing.expectEqual(Type.f64, c.ty);
    try std.testing.expectEqual(@as(f64, 42.2), c.value);

    const d = findBinding(result.bindings, "d").?;
    try std.testing.expectEqual(Type.length, d.ty);
    // 100 * 42.2 = 4220
    try std.testing.expectEqual(@as(f64, 4220.0), d.value);

    const e = findBinding(result.bindings, "e").?;
    try std.testing.expectEqual(Type.length, e.ty);
    // (100 + 20) * 42.2 = 120 * 42.2 = 5064
    try std.testing.expectEqual(@as(f64, 5064.0), e.value);
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
    try std.testing.expectEqual(@as(f64, 100.0), b.value);
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
    try std.testing.expectEqual(@as(f64, 100.0), head.value);
    try std.testing.expect(head.is_input);

    const x = findBinding(result.bindings, "x").?;
    try std.testing.expectEqual(@as(f64, 200.0), x.value);
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
    try std.testing.expectEqual(@as(f64, 120.0), result.bindings[0].value);
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
    try std.testing.expectEqual(@as(f64, 150.0), head.value);

    const x = findBinding(result.bindings, "x").?;
    // 150 * 2 = 300
    try std.testing.expectEqual(@as(f64, 300.0), x.value);
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
    try std.testing.expectEqual(@as(f64, 100.0), result.bindings[0].value);
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
    try std.testing.expectEqual(@as(f64, 100.0), head.value); // default

    const chest = findBinding(result.bindings, "chest").?;
    try std.testing.expectEqual(@as(f64, 1000.0), chest.value); // overridden

    const sum = findBinding(result.bindings, "sum").?;
    try std.testing.expectEqual(@as(f64, 1100.0), sum.value); // 100 + 1000
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

    try std.testing.expectEqual(@as(f64, 20.0), result.bindings[0].value);
    try std.testing.expect(result.bindings[0].is_input);
}
