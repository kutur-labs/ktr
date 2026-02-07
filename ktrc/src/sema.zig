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
    /// Ordered map of bindings in source order. The lowerer depends on
    /// iteration order matching definition order.
    symbols: std.StringArrayHashMap(Symbol),
    /// Resolved type for each expression node index.
    node_types: std.AutoHashMap(ast.NodeIndex, Type),
    diagnostics: []const Diagnostic,
    allocator: std.mem.Allocator,

    /// Returns true if any diagnostics were emitted during analysis.
    pub fn hasErrors(self: Sema) bool {
        return self.diagnostics.len > 0;
    }

    pub fn deinit(self: *Sema) void {
        self.symbols.deinit();
        self.node_types.deinit();
        self.allocator.free(self.diagnostics);
        self.* = undefined;
    }
};

const Analyzer = struct {
    tree: *const Ast,
    allocator: std.mem.Allocator,
    symbols: std.StringArrayHashMap(Symbol),
    node_types: std.AutoHashMap(ast.NodeIndex, Type),
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

        const ty = try self.resolveType(node.data.lhs);

        try self.symbols.put(name, .{ .ty = ty, .node = node_index });
    }

    fn resolveType(self: *Analyzer, node_index: ast.NodeIndex) std.mem.Allocator.Error!Type {
        const node = self.tree.nodes.get(node_index);
        const ty: Type = switch (node.tag) {
            .dimension_literal => .length,
            .percentage_literal => .percentage,
            .number_literal => .number,
            .identifier_ref => blk: {
                const ref_name = self.tree.tokenSlice(node.main_token);
                if (self.symbols.get(ref_name)) |sym| break :blk sym.ty;
                try self.addDiag(.undefined_reference, node.main_token);
                break :blk .poison;
            },
            .grouped_expression => try self.resolveType(node.data.lhs),
            .add, .sub, .mul, .div => blk: {
                const lhs_ty = try self.resolveType(node.data.lhs);
                const rhs_ty = try self.resolveType(node.data.rhs);

                // Poison propagates without cascading errors.
                if (lhs_ty == .poison or rhs_ty == .poison) break :blk .poison;

                break :blk try self.resolveArithmeticType(node.tag, lhs_ty, rhs_ty, node.main_token);
            },
            // Structurally impossible: the parser only produces expression nodes
            // as values in let_statement; root and let_statement never appear here.
            .root, .let_statement => unreachable,
        };
        try self.node_types.put(node_index, ty);
        return ty;
    }

    fn resolveArithmeticType(
        self: *Analyzer,
        op: ast.Node.Tag,
        lhs: Type,
        rhs: Type,
        token: u32,
    ) std.mem.Allocator.Error!Type {
        // number op number -> number
        if (lhs == .number and rhs == .number) return .number;

        // length +/- length -> length
        if (lhs == .length and rhs == .length and (op == .add or op == .sub))
            return .length;

        // length * number -> length, number * length -> length
        if (op == .mul) {
            if (lhs == .length and rhs == .number) return .length;
            if (lhs == .number and rhs == .length) return .length;
        }

        // length / number -> length
        if (op == .div and lhs == .length and rhs == .number)
            return .length;

        // length / length -> number (ratio)
        if (op == .div and lhs == .length and rhs == .length)
            return .number;

        try self.addDiag(.type_mismatch, token);
        return .poison;
    }
};

/// Run semantic analysis on a parsed AST.
pub fn analyze(allocator: std.mem.Allocator, tree: *const Ast) std.mem.Allocator.Error!Sema {
    var a = Analyzer{
        .tree = tree,
        .allocator = allocator,
        .symbols = std.StringArrayHashMap(Symbol).init(allocator),
        .node_types = std.AutoHashMap(ast.NodeIndex, Type).init(allocator),
        .diagnostics = std.ArrayList(Diagnostic).empty,
    };
    errdefer a.symbols.deinit();
    errdefer a.node_types.deinit();
    errdefer a.diagnostics.deinit(allocator);

    try a.analyzeRoot();

    return .{
        .symbols = a.symbols,
        .node_types = a.node_types,
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

test "analyze: f64 + f64 -> number" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "let x = 1 + 2";

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    try std.testing.expect(!sem.hasErrors());
    try std.testing.expectEqual(.number, sem.symbols.get("x").?.ty);
}

test "analyze: length + length -> length" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "let x = 100mm + 200mm";

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    try std.testing.expect(!sem.hasErrors());
    try std.testing.expectEqual(.length, sem.symbols.get("x").?.ty);
}

test "analyze: length * f64 -> length" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "let x = 100mm * 2";

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    try std.testing.expect(!sem.hasErrors());
    try std.testing.expectEqual(.length, sem.symbols.get("x").?.ty);
}

test "analyze: f64 * length -> length" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "let a = 100mm let x = 2 * a";

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    try std.testing.expect(!sem.hasErrors());
    try std.testing.expectEqual(.length, sem.symbols.get("x").?.ty);
}

test "analyze: length / f64 -> length" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "let x = 100mm / 2";

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    try std.testing.expect(!sem.hasErrors());
    try std.testing.expectEqual(.length, sem.symbols.get("x").?.ty);
}

test "analyze: length / length -> number (ratio)" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "let x = 100mm / 50mm";

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    try std.testing.expect(!sem.hasErrors());
    try std.testing.expectEqual(.number, sem.symbols.get("x").?.ty);
}

test "analyze: type mismatch length + f64" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "let x = 100mm + 2";

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    try std.testing.expect(sem.hasErrors());
    try std.testing.expectEqual(1, sem.diagnostics.len);
    try std.testing.expectEqual(.type_mismatch, sem.diagnostics[0].tag);
}

test "analyze: grouped expression preserves type" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "let x = (1 + 2) * 3";

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    try std.testing.expect(!sem.hasErrors());
    try std.testing.expectEqual(.number, sem.symbols.get("x").?.ty);
}

test "analyze: reference in arithmetic" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "let a = 2 let x = a * 3";

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    try std.testing.expect(!sem.hasErrors());
    try std.testing.expectEqual(.number, sem.symbols.get("x").?.ty);
}

test "analyze: poison propagation in arithmetic" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "let x = unknown * 2";

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    // One error for the undefined ref, but poison propagates through the mul.
    try std.testing.expectEqual(1, sem.diagnostics.len);
    try std.testing.expectEqual(.undefined_reference, sem.diagnostics[0].tag);
    try std.testing.expectEqual(.poison, sem.symbols.get("x").?.ty);
}
