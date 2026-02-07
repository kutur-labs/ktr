comptime {
    _ = @import("unit.zig");
    _ = @import("lexer.zig");
    _ = @import("ast.zig");
    _ = @import("parser.zig");
    _ = @import("sema.zig");
    _ = @import("ir.zig");
    _ = @import("lower.zig");
    _ = @import("ir_emit.zig");
    _ = @import("ir_parse.zig");
    _ = @import("ir_decompile.zig");
}
