const std = @import("std");

pub const LengthUnit = enum(u8) {
    mm,
    cm,

    pub const map = std.StaticStringMap(LengthUnit).initComptime(.{
        .{ "mm", .mm },
        .{ "cm", .cm },
    });

    pub fn fromStr(s: []const u8) ?LengthUnit {
        return map.get(s);
    }

    pub fn toStr(self: LengthUnit) []const u8 {
        return @tagName(self);
    }
};

// --- Tests ---

test "unit round-trip through string" {
    inline for (.{ LengthUnit.mm, LengthUnit.cm }) |u| {
        try std.testing.expectEqual(u, LengthUnit.fromStr(u.toStr()).?);
    }
}
