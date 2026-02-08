const std = @import("std");
pub const LengthUnit = @import("unit.zig").LengthUnit;

pub const Type = enum(u8) {
    f64,
    length,
    percentage,

    pub fn toStr(self: Type) []const u8 {
        return @tagName(self);
    }

    pub fn fromStr(s: []const u8) ?Type {
        return std.meta.stringToEnum(Type, s);
    }
};

pub const Value = struct {
    number: f64,
    unit: ?LengthUnit, // non-null only for Type.length

    pub fn eql(a: Value, b: Value) bool {
        if (a.number != b.number) return false;
        return a.unit == b.unit;
    }

    /// Write the numeric part of the value, using integer form when possible.
    pub fn writeNumber(self: Value, writer: anytype) !void {
        try formatF64(writer, self.number);
    }

    /// Parse a numeric value with optional unit suffix.
    ///
    /// Handles dimension values (`100mm`, `25cm`) and bare numbers (`42`, `3.14`).
    /// Does NOT handle `%` suffix; that is a source-level concept.
    pub fn parse(text: []const u8) error{InvalidFormat}!Value {
        // Find the boundary between numeric and suffix characters.
        var split: usize = text.len;
        for (text, 0..) |c, i| {
            if (!std.ascii.isDigit(c) and c != '.' and c != '-') {
                split = i;
                break;
            }
        }

        const num_text = text[0..split];
        const suffix = text[split..];

        const number = std.fmt.parseFloat(f64, num_text) catch return error.InvalidFormat;

        if (suffix.len == 0) {
            return .{ .number = number, .unit = null };
        }

        const unit = LengthUnit.fromStr(suffix) orelse return error.InvalidFormat;
        return .{ .number = number, .unit = unit };
    }
};

pub const Op = enum(u8) {
    add,
    sub,
    mul,
    div,

    pub fn toStr(self: Op) []const u8 {
        return @tagName(self);
    }

    pub fn fromStr(s: []const u8) ?Op {
        return std.meta.stringToEnum(Op, s);
    }
};

pub const Operand = union(enum) {
    /// Reference to another binding: `%name`.
    ref: []const u8,
    /// Literal value: `42`, `100mm`.
    literal: Value,

    pub fn eql(a: Operand, b: Operand) bool {
        if (std.meta.activeTag(a) != std.meta.activeTag(b)) return false;
        return switch (a) {
            .ref => |ar| std.mem.eql(u8, ar, b.ref),
            .literal => |av| av.eql(b.literal),
        };
    }
};

pub const Inst = struct {
    name: []const u8,
    ty: Type,
    rhs: Rhs,

    pub const Builtin = struct {
        op: Op,
        lhs: Operand,
        rhs: Operand,
    };

    pub const Rhs = union(enum) {
        /// Direct constant value: `%x : length = 100mm`.
        constant: Value,
        /// Alias of another binding: `%y : length = %x`.
        copy: []const u8,
        /// Builtin operation: `%z : length = mul %x 2`.
        builtin: Builtin,

        pub fn eql(a: Rhs, b: Rhs) bool {
            if (std.meta.activeTag(a) != std.meta.activeTag(b)) return false;
            return switch (a) {
                .constant => |av| av.eql(b.constant),
                .copy => |ar| std.mem.eql(u8, ar, b.copy),
                .builtin => |ab| ab.op == b.builtin.op and ab.lhs.eql(b.builtin.lhs) and ab.rhs.eql(b.builtin.rhs),
            };
        }
    };

    pub fn eql(a: Inst, b: Inst) bool {
        if (!std.mem.eql(u8, a.name, b.name)) return false;
        if (a.ty != b.ty) return false;
        return a.rhs.eql(b.rhs);
    }
};

pub const Ir = struct {
    version: u32 = 1,
    instructions: []const Inst,
    arena: std.heap.ArenaAllocator,

    pub fn deinit(self: *Ir) void {
        self.arena.deinit();
        self.* = undefined;
    }

    /// Compares two Ir values for structural equality (ignoring arena).
    pub fn eql(a: Ir, b: Ir) bool {
        if (a.version != b.version) return false;
        if (a.instructions.len != b.instructions.len) return false;
        for (a.instructions, b.instructions) |ai, bi| {
            if (!ai.eql(bi)) return false;
        }
        return true;
    }
};

/// Write an f64 using integer form when the value is exactly representable
/// as an integer (e.g. `100` instead of `1e2` or `100.0`).
pub fn formatF64(writer: anytype, value: f64) !void {
    if (value == @trunc(value) and !std.math.isInf(value)) {
        try writer.print("{d}", .{@as(i64, @intFromFloat(value))});
    } else {
        try writer.print("{d}", .{value});
    }
}

/// Returns true if a binding name is a compiler-generated temporary.
/// Convention from lower.zig: temps are purely numeric (`0`, `1`, ...).
pub fn isTemp(name: []const u8) bool {
    if (name.len == 0) return false;
    for (name) |c| {
        if (!std.ascii.isDigit(c)) return false;
    }
    return true;
}

// --- Tests ---

test "type round-trip through string" {
    inline for (.{ Type.f64, Type.length, Type.percentage }) |ty| {
        try std.testing.expectEqual(ty, Type.fromStr(ty.toStr()).?);
    }
}

test "value parse" {
    const dim = try Value.parse("100mm");
    try std.testing.expectEqual(@as(f64, 100.0), dim.number);
    try std.testing.expectEqual(LengthUnit.mm, dim.unit.?);

    const bare = try Value.parse("42");
    try std.testing.expectEqual(@as(f64, 42.0), bare.number);
    try std.testing.expectEqual(@as(?LengthUnit, null), bare.unit);

    const cm = try Value.parse("25cm");
    try std.testing.expectEqual(@as(f64, 25.0), cm.number);
    try std.testing.expectEqual(LengthUnit.cm, cm.unit.?);

    try std.testing.expectError(error.InvalidFormat, Value.parse("abc"));
    try std.testing.expectError(error.InvalidFormat, Value.parse("100xyz"));
}

test "ir deinit does not leak" {
    const gpa = std.testing.allocator;
    var arena = std.heap.ArenaAllocator.init(gpa);
    const ally = arena.allocator();

    const insts = try ally.alloc(Inst, 1);
    insts[0] = .{
        .name = try ally.dupe(u8, "x"),
        .ty = .length,
        .rhs = .{ .constant = .{ .number = 100.0, .unit = .mm } },
    };

    var ir = Ir{
        .version = 1,
        .instructions = insts,
        .arena = arena,
    };
    ir.deinit();
    // If deinit leaked, the testing allocator would catch it.
}

test "ir structural equality" {
    const gpa = std.testing.allocator;

    // Build first Ir.
    var arena_a = std.heap.ArenaAllocator.init(gpa);
    const ally_a = arena_a.allocator();
    const insts_a = try ally_a.alloc(Inst, 2);
    insts_a[0] = .{
        .name = try ally_a.dupe(u8, "x"),
        .ty = .length,
        .rhs = .{ .constant = .{ .number = 100.0, .unit = .mm } },
    };
    insts_a[1] = .{
        .name = try ally_a.dupe(u8, "y"),
        .ty = .length,
        .rhs = .{ .copy = try ally_a.dupe(u8, "x") },
    };
    var ir_a = Ir{ .instructions = insts_a, .arena = arena_a };
    defer ir_a.deinit();

    // Build second identical Ir.
    var arena_b = std.heap.ArenaAllocator.init(gpa);
    const ally_b = arena_b.allocator();
    const insts_b = try ally_b.alloc(Inst, 2);
    insts_b[0] = .{
        .name = try ally_b.dupe(u8, "x"),
        .ty = .length,
        .rhs = .{ .constant = .{ .number = 100.0, .unit = .mm } },
    };
    insts_b[1] = .{
        .name = try ally_b.dupe(u8, "y"),
        .ty = .length,
        .rhs = .{ .copy = try ally_b.dupe(u8, "x") },
    };
    var ir_b = Ir{ .instructions = insts_b, .arena = arena_b };
    defer ir_b.deinit();

    try std.testing.expect(ir_a.eql(ir_b));
}
