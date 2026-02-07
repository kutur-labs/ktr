const std = @import("std");
const ir = @import("ir.zig");
const Ir = ir.Ir;
const Inst = ir.Inst;
const Value = ir.Value;
const LengthUnit = ir.LengthUnit;
const Type = ir.Type;
const Op = ir.Op;
const Operand = ir.Operand;

pub const Error = error{
    InvalidFormat,
} || std.mem.Allocator.Error;

/// Parse a `%`-prefixed name token, returning the name without the sigil.
fn parseName(ally: std.mem.Allocator, token: []const u8) Error![]const u8 {
    if (token.len == 0 or token[0] != '%') return error.InvalidFormat;
    const body = token[1..];
    if (body.len == 0) return error.InvalidFormat;
    return try ally.dupe(u8, body);
}

/// Skip leading whitespace and return the remainder.
fn skipWs(s: []const u8) []const u8 {
    return std.mem.trimLeft(u8, s, " \t");
}

/// Split at the first occurrence of `delim`, returning (before, after).
fn splitOnce(s: []const u8, delim: u8) ?struct { []const u8, []const u8 } {
    if (std.mem.indexOfScalar(u8, s, delim)) |idx| {
        return .{ s[0..idx], s[idx + 1 ..] };
    }
    return null;
}

/// Parse a single operand token (either `%ref` or a literal value).
fn parseOperand(ally: std.mem.Allocator, token: []const u8) Error!Operand {
    if (token.len > 0 and token[0] == '%') {
        return .{ .ref = try parseName(ally, token) };
    }
    return .{ .literal = Value.parse(token) catch return error.InvalidFormat };
}

/// Try to parse a builtin RHS: `op operand operand` (e.g., `mul %a 2`).
/// Returns null if the first token is not a known op keyword.
fn parseBuiltinRhs(ally: std.mem.Allocator, text: []const u8) Error!?Inst.Rhs {
    // Find the first space to extract the op keyword.
    const first_space = std.mem.indexOfScalar(u8, text, ' ') orelse return null;
    const op_str = text[0..first_space];
    const op = Op.fromStr(op_str) orelse return null;

    // Parse the two operands after the op keyword.
    const rest = skipWs(text[first_space + 1 ..]);

    // Find the boundary between the two operands. Operands are separated by
    // whitespace. The first operand is either a `%name` or a literal.
    const operand_split = findOperandBoundary(rest) orelse return error.InvalidFormat;
    const lhs_text = std.mem.trimRight(u8, rest[0..operand_split], " \t");
    const rhs_text = skipWs(rest[operand_split..]);

    if (lhs_text.len == 0 or rhs_text.len == 0) return error.InvalidFormat;

    const lhs = try parseOperand(ally, lhs_text);
    const rhs = try parseOperand(ally, rhs_text);

    return .{ .builtin = .{ .op = op, .lhs = lhs, .rhs = rhs } };
}

/// Find the boundary index between two operands in a string like `%a 2` or `100mm %b`.
/// Returns the index of the first whitespace character separating them.
fn findOperandBoundary(text: []const u8) ?usize {
    for (text, 0..) |c, i| {
        if (std.ascii.isWhitespace(c)) return i;
    }
    return null;
}

/// Parse `.ktrir` text into an `Ir`.
///
/// The returned `Ir` owns all its memory via an arena; call `Ir.deinit()`
/// when done.
pub fn parse(gpa: std.mem.Allocator, source: []const u8) Error!Ir {
    var arena = std.heap.ArenaAllocator.init(gpa);
    errdefer arena.deinit();
    const ally = arena.allocator();

    var instructions = std.ArrayList(Inst).empty;
    var version: u32 = 1;
    var header_seen = false;

    var iter = std.mem.splitScalar(u8, source, '\n');
    while (iter.next()) |raw_line| {
        const line = std.mem.trimRight(u8, raw_line, " \t\r");

        // Skip blank lines.
        if (line.len == 0) continue;

        // Comment or header line.
        if (line[0] == '#') {
            if (!header_seen) {
                // Parse header: `# ktr-ir v<N>`
                const trimmed = std.mem.trimLeft(u8, line[1..], " \t");
                if (std.mem.startsWith(u8, trimmed, "ktr-ir v")) {
                    const ver_str = trimmed["ktr-ir v".len..];
                    version = std.fmt.parseInt(u32, ver_str, 10) catch return error.InvalidFormat;
                    header_seen = true;
                }
            }
            continue;
        }

        // Instruction line: `%<name> : <type> = <rhs>`
        if (!header_seen) return error.InvalidFormat;

        // Split on '=' to get LHS and RHS.
        const eq_split = splitOnce(line, '=') orelse return error.InvalidFormat;
        const lhs_part = std.mem.trimRight(u8, eq_split[0], " \t");
        const rhs_text = skipWs(eq_split[1]);

        // Parse LHS: `%name : type`
        const colon_split = splitOnce(lhs_part, ':') orelse return error.InvalidFormat;
        const ref_text = std.mem.trimRight(u8, colon_split[0], " \t");
        const type_text = std.mem.trim(u8, colon_split[1], " \t");

        const name = try parseName(ally, ref_text);
        const ty = Type.fromStr(type_text) orelse return error.InvalidFormat;

        // Parse RHS: `%name` (copy), `op operand operand` (builtin), or literal (constant).
        const rhs: Inst.Rhs = blk: {
            if (rhs_text.len > 0 and rhs_text[0] == '%') {
                break :blk .{ .copy = try parseName(ally, rhs_text) };
            }
            // Try to parse as builtin op: first token is the op keyword.
            if (try parseBuiltinRhs(ally, rhs_text)) |builtin_rhs| {
                break :blk builtin_rhs;
            }
            // Fall back to literal constant.
            break :blk .{ .constant = Value.parse(rhs_text) catch return error.InvalidFormat };
        };

        try instructions.append(ally, .{
            .name = name,
            .ty = ty,
            .rhs = rhs,
        });
    }

    return .{
        .version = version,
        .instructions = try instructions.toOwnedSlice(ally),
        .arena = arena,
    };
}

// --- Tests ---

test "parse: empty program" {
    const allocator = std.testing.allocator;
    var result = try parse(allocator, "# ktr-ir v1\n");
    defer result.deinit();

    try std.testing.expectEqual(1, result.version);
    try std.testing.expectEqual(0, result.instructions.len);
}

test "parse: single dimension literal" {
    const allocator = std.testing.allocator;
    const source =
        \\# ktr-ir v1
        \\
        \\%x : length = 100mm
    ;

    var result = try parse(allocator, source);
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

test "parse: copy reference" {
    const allocator = std.testing.allocator;
    const source =
        \\# ktr-ir v1
        \\
        \\%x : length = 100mm
        \\%y : length = %x
    ;

    var result = try parse(allocator, source);
    defer result.deinit();

    try std.testing.expectEqual(2, result.instructions.len);

    const inst_y = result.instructions[1];
    try std.testing.expectEqualStrings("y", inst_y.name);
    try std.testing.expectEqual(Type.length, inst_y.ty);

    switch (inst_y.rhs) {
        .copy => |name| try std.testing.expectEqualStrings("x", name),
        else => return error.TestUnexpectedResult,
    }
}

test "parse: mixed types" {
    const allocator = std.testing.allocator;
    const source =
        \\# ktr-ir v1
        \\
        \\%x : length = 100mm
        \\%p : percentage = 50
        \\%n : f64 = 42
        \\%y : length = %x
    ;

    var result = try parse(allocator, source);
    defer result.deinit();

    try std.testing.expectEqual(4, result.instructions.len);

    try std.testing.expectEqualStrings("x", result.instructions[0].name);
    try std.testing.expectEqual(Type.length, result.instructions[0].ty);

    try std.testing.expectEqualStrings("p", result.instructions[1].name);
    try std.testing.expectEqual(Type.percentage, result.instructions[1].ty);

    try std.testing.expectEqualStrings("n", result.instructions[2].name);
    try std.testing.expectEqual(Type.f64, result.instructions[2].ty);

    try std.testing.expectEqualStrings("y", result.instructions[3].name);
    switch (result.instructions[3].rhs) {
        .copy => |name| try std.testing.expectEqualStrings("x", name),
        else => return error.TestUnexpectedResult,
    }
}

test "parse: invalid header" {
    const allocator = std.testing.allocator;
    try std.testing.expectError(error.InvalidFormat, parse(allocator, "%x : length = 100mm\n"));
}

test "parse: cm unit" {
    const allocator = std.testing.allocator;
    const source =
        \\# ktr-ir v1
        \\
        \\%w : length = 25cm
    ;

    var result = try parse(allocator, source);
    defer result.deinit();

    switch (result.instructions[0].rhs) {
        .constant => |v| {
            try std.testing.expectEqual(@as(f64, 25.0), v.number);
            try std.testing.expectEqual(LengthUnit.cm, v.unit.?);
        },
        else => return error.TestUnexpectedResult,
    }
}

test "parse: builtin op with ref and literal" {
    const allocator = std.testing.allocator;
    const source =
        \\# ktr-ir v1
        \\
        \\%a : length = 100mm
        \\%x : length = mul %a 2
    ;

    var result = try parse(allocator, source);
    defer result.deinit();

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

test "parse: builtin op with two refs" {
    const allocator = std.testing.allocator;
    const source =
        \\# ktr-ir v1
        \\
        \\%a : f64 = 10
        \\%b : f64 = 20
        \\%x : f64 = add %a %b
    ;

    var result = try parse(allocator, source);
    defer result.deinit();

    try std.testing.expectEqual(3, result.instructions.len);

    const inst = result.instructions[2];
    switch (inst.rhs) {
        .builtin => |b| {
            try std.testing.expectEqual(Op.add, b.op);
            try std.testing.expect(b.lhs == .ref);
            try std.testing.expectEqualStrings("a", b.lhs.ref);
            try std.testing.expect(b.rhs == .ref);
            try std.testing.expectEqualStrings("b", b.rhs.ref);
        },
        else => return error.TestUnexpectedResult,
    }
}

test "parse: builtin op with two literals" {
    const allocator = std.testing.allocator;
    const source =
        \\# ktr-ir v1
        \\
        \\%x : f64 = add 2 3
    ;

    var result = try parse(allocator, source);
    defer result.deinit();

    try std.testing.expectEqual(1, result.instructions.len);

    const inst = result.instructions[0];
    switch (inst.rhs) {
        .builtin => |b| {
            try std.testing.expectEqual(Op.add, b.op);
            try std.testing.expect(b.lhs == .literal);
            try std.testing.expectEqual(@as(f64, 2.0), b.lhs.literal.number);
            try std.testing.expect(b.rhs == .literal);
            try std.testing.expectEqual(@as(f64, 3.0), b.rhs.literal.number);
        },
        else => return error.TestUnexpectedResult,
    }
}

test "parse: builtin op with dimension literals" {
    const allocator = std.testing.allocator;
    const source =
        \\# ktr-ir v1
        \\
        \\%x : length = add 100mm 200mm
    ;

    var result = try parse(allocator, source);
    defer result.deinit();

    try std.testing.expectEqual(1, result.instructions.len);

    const inst = result.instructions[0];
    switch (inst.rhs) {
        .builtin => |b| {
            try std.testing.expectEqual(Op.add, b.op);
            try std.testing.expect(b.lhs == .literal);
            try std.testing.expectEqual(@as(f64, 100.0), b.lhs.literal.number);
            try std.testing.expectEqual(LengthUnit.mm, b.lhs.literal.unit.?);
            try std.testing.expect(b.rhs == .literal);
            try std.testing.expectEqual(@as(f64, 200.0), b.rhs.literal.number);
        },
        else => return error.TestUnexpectedResult,
    }
}
