const std = @import("std");
const ast = @import("ast.zig");
const Ast = ast.Ast;
const Diagnostic = ast.Diagnostic;

pub const Type = enum {
    /// A length value with a unit (mm, cm).
    length,
    /// A percentage value (%).
    percentage,
    /// A bare number without a unit.
    number,
    /// Unresolvable value; suppresses cascading diagnostics.
    poison,
};

pub const Symbol = struct {
    ty: Type,
    /// AST node index of the defining let_statement.
    node: ast.NodeIndex,
};

/// Result of semantic analysis. Symbol names are slices borrowed from the
/// original source buffer (via the Ast), so the caller must keep both the
/// source and the Ast alive for the lifetime of this Sema.
pub const Sema = struct {
    symbols: std.StringArrayHashMap(Symbol),
    diagnostics: []const Diagnostic,
    allocator: std.mem.Allocator,

    /// Returns true if any diagnostics were emitted during analysis.
    pub fn hasErrors(self: Sema) bool {
        return self.diagnostics.len > 0;
    }

    pub fn deinit(self: *Sema) void {
        self.symbols.deinit();
        self.allocator.free(self.diagnostics);
        self.* = undefined;
    }
};

const Analyzer = struct {
    tree: *const Ast,
    allocator: std.mem.Allocator,
    symbols: std.StringArrayHashMap(Symbol),
    diagnostics: std.ArrayList(Diagnostic),

    fn addDiag(self: *Analyzer, tag: Diagnostic.Tag, token: u32) std.mem.Allocator.Error!void {
        try self.diagnostics.append(self.allocator, .{ .tag = tag, .token = token });
    }

    fn analyzeRoot(self: *Analyzer) std.mem.Allocator.Error!void {
        const statements = self.tree.rootStatements(0);
        for (statements) |stmt_index| {
            const node = self.tree.nodes.get(stmt_index);
            switch (node.tag) {
                .let_statement => try self.analyzeLet(node, stmt_index),
                else => {},
            }
        }
    }

    fn analyzeLet(self: *Analyzer, node: ast.Node, node_index: ast.NodeIndex) std.mem.Allocator.Error!void {
        const name = self.tree.tokenSlice(node.main_token + 1);

        if (self.symbols.contains(name)) {
            try self.addDiag(.duplicate_binding, node.main_token);
            return;
        }

        const value_node = self.tree.nodes.get(node.data.lhs);
        const ty = try self.resolveType(value_node);

        try self.symbols.put(name, .{ .ty = ty, .node = node_index });
    }

    fn resolveType(self: *Analyzer, node: ast.Node) std.mem.Allocator.Error!Type {
        return switch (node.tag) {
            .dimension_literal => .length,
            .percentage_literal => .percentage,
            .number_literal => .number,
            .identifier_ref => {
                const ref_name = self.tree.tokenSlice(node.main_token);
                if (self.symbols.get(ref_name)) |sym| return sym.ty;
                try self.addDiag(.undefined_reference, node.main_token);
                return .poison;
            },
            // Structurally impossible: the parser only produces expression nodes
            // as values in let_statement; root and let_statement never appear here.
            .root, .let_statement => unreachable,
        };
    }
};

/// Run semantic analysis on a parsed AST.
pub fn analyze(allocator: std.mem.Allocator, tree: *const Ast) std.mem.Allocator.Error!Sema {
    var a = Analyzer{
        .tree = tree,
        .allocator = allocator,
        .symbols = std.StringArrayHashMap(Symbol).init(allocator),
        .diagnostics = std.ArrayList(Diagnostic).empty,
    };
    errdefer a.symbols.deinit();
    errdefer a.diagnostics.deinit(allocator);

    try a.analyzeRoot();

    return .{
        .symbols = a.symbols,
        .diagnostics = try a.diagnostics.toOwnedSlice(allocator),
        .allocator = allocator,
    };
}

// --- Tests ---

const parser = @import("parser.zig");

test "analyze: resolves types" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "let x = 100mm";

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sema = try analyze(allocator, &tree);
    defer sema.deinit();

    try std.testing.expect(!sema.hasErrors());
    const sym = sema.symbols.get("x").?;
    try std.testing.expectEqual(.length, sym.ty);
}

test "analyze: duplicate binding" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "let x = 100mm let x = 200cm";

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sema = try analyze(allocator, &tree);
    defer sema.deinit();

    try std.testing.expect(sema.hasErrors());
    try std.testing.expectEqual(1, sema.diagnostics.len);
    try std.testing.expectEqual(.duplicate_binding, sema.diagnostics[0].tag);
    // Second "let" is the duplicate; token index points into tree.tokens.
    try std.testing.expectEqualStrings(tree.tokenSlice(sema.diagnostics[0].token), "let");
}

test "analyze: unitless number" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "let a = 42";

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sema = try analyze(allocator, &tree);
    defer sema.deinit();

    try std.testing.expect(!sema.hasErrors());
    const sym = sema.symbols.get("a").?;
    try std.testing.expectEqual(.number, sym.ty);
}

test "analyze: percentage literal" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "let p = 50%";

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sema = try analyze(allocator, &tree);
    defer sema.deinit();

    try std.testing.expect(!sema.hasErrors());
    try std.testing.expectEqual(.percentage, sema.symbols.get("p").?.ty);
}

test "analyze: multiple bindings" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "let a = 100mm let b = 50% let c = 42";

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sema = try analyze(allocator, &tree);
    defer sema.deinit();

    try std.testing.expect(!sema.hasErrors());
    try std.testing.expectEqual(3, sema.symbols.count());
    try std.testing.expectEqual(.length, sema.symbols.get("a").?.ty);
    try std.testing.expectEqual(.percentage, sema.symbols.get("b").?.ty);
    try std.testing.expectEqual(.number, sema.symbols.get("c").?.ty);
}

test "analyze: identifier reference propagates type" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "let x = 100mm let y = x";

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sema = try analyze(allocator, &tree);
    defer sema.deinit();

    try std.testing.expect(!sema.hasErrors());
    try std.testing.expectEqual(.length, sema.symbols.get("x").?.ty);
    try std.testing.expectEqual(.length, sema.symbols.get("y").?.ty);
}

test "analyze: undefined reference" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "let y = x";

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sema = try analyze(allocator, &tree);
    defer sema.deinit();

    try std.testing.expect(sema.hasErrors());
    try std.testing.expectEqual(1, sema.diagnostics.len);
    try std.testing.expectEqual(.undefined_reference, sema.diagnostics[0].tag);
}

test "analyze: poison suppresses cascading errors" {
    const allocator = std.testing.allocator;
    // `unknown` is undefined, so `y` gets poison. `z = y` should NOT emit a second error.
    const source: [:0]const u8 = "let y = unknown let z = y";

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sema = try analyze(allocator, &tree);
    defer sema.deinit();

    // Only one diagnostic: `unknown` is undefined. No cascading error for `z = y`.
    try std.testing.expectEqual(1, sema.diagnostics.len);
    try std.testing.expectEqual(.undefined_reference, sema.diagnostics[0].tag);

    // `y` is in the symbol table with poison type.
    try std.testing.expectEqual(.poison, sema.symbols.get("y").?.ty);
    // `z` is also poison (propagated), but no extra diagnostic.
    try std.testing.expectEqual(.poison, sema.symbols.get("z").?.ty);
}
