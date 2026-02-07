const std = @import("std");
const ir = @import("ir.zig");
const Ir = ir.Ir;
const Inst = ir.Inst;
const Value = ir.Value;
const LengthUnit = ir.LengthUnit;
const Type = ir.Type;

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

        // Parse RHS: either a `%name` (copy) or a literal value (constant).
        const rhs: Inst.Rhs = if (rhs_text.len > 0 and rhs_text[0] == '%') blk: {
            break :blk .{ .copy = try parseName(ally, rhs_text) };
        } else blk: {
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
        .copy => return error.TestUnexpectedResult,
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
        .constant => return error.TestUnexpectedResult,
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
        .constant => return error.TestUnexpectedResult,
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
        .copy => return error.TestUnexpectedResult,
    }
}
