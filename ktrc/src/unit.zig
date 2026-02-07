const std = @import("std");

pub const LengthUnit = enum(u8) {
    mm,
    cm,

    pub fn fromStr(s: []const u8) ?LengthUnit {
        return std.meta.stringToEnum(LengthUnit, s);
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
