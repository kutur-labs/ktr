const std = @import("std");
const ast = @import("ast.zig");
const Ast = ast.Ast;
const Diagnostic = ast.Diagnostic;
const ir = @import("ir.zig");

pub const Type = enum {
    /// A length value with a unit (mm, cm).
    length,
    /// A percentage value (%).
    percentage,
    /// A bare number without a unit.
    f64,
    /// A 2D coordinate (x: length, y: length).
    point,
    /// Cubic Bezier curve (4 control points).
    bezier,
    /// Straight segment between two points.
    line,
    /// Unresolvable value; suppresses cascading diagnostics.
    poison,
};

pub const Symbol = struct {
    ty: Type,
    /// AST node index of the defining statement (let_statement or input_statement).
    node: ast.NodeIndex,
    kind: Kind,

    pub const Kind = enum { let_binding, input };
};

/// Result of semantic analysis. Symbol names are slices borrowed from the
/// original source buffer (via the Ast), so the caller must keep both the
/// source and the Ast alive for the lifetime of this Sema.
pub const Sema = struct {
    /// Ordered map of bindings in source order. The lowerer depends on
    /// iteration order matching definition order.
    symbols: std.StringArrayHashMap(Symbol),
    /// Resolved type for each AST node, indexed by NodeIndex.
    /// Only expression nodes have meaningful values; other slots are undefined.
    node_types: []Type,
    diagnostics: []const Diagnostic,
    allocator: std.mem.Allocator,

    /// Returns true if any diagnostics were emitted during analysis.
    pub fn hasErrors(self: Sema) bool {
        return self.diagnostics.len > 0;
    }

    pub fn deinit(self: *Sema) void {
        self.symbols.deinit();
        self.allocator.free(self.node_types);
        self.allocator.free(self.diagnostics);
        self.* = undefined;
    }
};

const Analyzer = struct {
    tree: *const Ast,
    allocator: std.mem.Allocator,
    symbols: std.StringArrayHashMap(Symbol),
    node_types: []Type,
    diagnostics: std.ArrayList(Diagnostic),

    fn addDiag(self: *Analyzer, tag: Diagnostic.Tag, token: u32) std.mem.Allocator.Error!void {
        try self.diagnostics.append(self.allocator, .{ .tag = tag, .token = token });
    }

    fn analyzeRoot(self: *Analyzer) std.mem.Allocator.Error!void {
        const statements = self.tree.rootStatements(0);
        for (statements) |stmt_index| {
            const node = self.tree.nodes.get(stmt_index);
            switch (node.tag) {
                .let_statement => try self.analyzeBinding(node, stmt_index, .let_binding),
                .input_statement => try self.analyzeBinding(node, stmt_index, .input),
                else => {},
            }
        }
    }

    fn analyzeBinding(self: *Analyzer, node: ast.Node, node_index: ast.NodeIndex, kind: Symbol.Kind) std.mem.Allocator.Error!void {
        const name = self.tree.tokenSlice(node.main_token + 1);

        if (self.symbols.contains(name)) {
            try self.addDiag(.duplicate_binding, node.main_token);
            return;
        }

        const ty = try self.resolveType(node.data.lhs);

        try self.symbols.put(name, .{ .ty = ty, .node = node_index, .kind = kind });
    }

    fn resolveType(self: *Analyzer, node_index: ast.NodeIndex) std.mem.Allocator.Error!Type {
        const node = self.tree.nodes.get(node_index);
        const ty: Type = switch (node.tag) {
            .dimension_literal => .length,
            .percentage_literal => .percentage,
            .number_literal => .f64,
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
            .fn_call => try self.resolveCallType(node_index),
            // Structurally impossible: the parser only produces expression nodes
            // as values in statements; root, let_statement and input_statement
            // never appear here.
            .root, .let_statement, .input_statement => unreachable,
        };
        self.node_types[node_index] = ty;
        return ty;
    }

    fn resolveCallType(self: *Analyzer, node_index: ast.NodeIndex) std.mem.Allocator.Error!Type {
        const node = self.tree.nodes.get(node_index);
        const name = self.tree.tokenSlice(node.main_token);
        const args = self.tree.callArgs(node_index);

        // Look up in the centralized builtin registry (ir.zig).
        const sig = ir.builtin_sigs.get(name) orelse {
            try self.addDiag(.unknown_function, node.main_token);
            return .poison;
        };

        // Check argument count.
        if (args.len != sig.params.len) {
            try self.addDiag(.wrong_argument_count, node.main_token);
            return .poison;
        }

        // Check each argument type.
        var has_poison = false;
        for (args, sig.params) |arg_idx, expected_ir_ty| {
            const actual_ty = try self.resolveType(arg_idx);
            if (actual_ty == .poison) {
                has_poison = true;
                continue;
            }
            const expected_ty = mapFromIrType(expected_ir_ty);
            if (actual_ty != expected_ty) {
                try self.addDiag(.argument_type_mismatch, self.tree.nodes.items(.main_token)[arg_idx]);
            }
        }

        if (has_poison) return .poison;
        return mapFromIrType(sig.ret);
    }

    /// Map an ir.Type to a sema.Type. The IR type enum is a subset of the
    /// sema type enum (no poison), so this is always valid.
    fn mapFromIrType(ir_ty: ir.Type) Type {
        return std.meta.stringToEnum(Type, @tagName(ir_ty)).?;
    }

    fn resolveArithmeticType(
        self: *Analyzer,
        op: ast.Node.Tag,
        lhs: Type,
        rhs: Type,
        token: u32,
    ) std.mem.Allocator.Error!Type {
        // f64 op f64 -> f64
        if (lhs == .f64 and rhs == .f64) return .f64;

        // length +/- length -> length
        if (lhs == .length and rhs == .length and (op == .add or op == .sub))
            return .length;

        // length * f64 -> length, f64 * length -> length
        if (op == .mul) {
            if (lhs == .length and rhs == .f64) return .length;
            if (lhs == .f64 and rhs == .length) return .length;
        }

        // length / f64 -> length
        if (op == .div and lhs == .length and rhs == .f64)
            return .length;

        // length / length -> f64 (ratio)
        if (op == .div and lhs == .length and rhs == .length)
            return .f64;

        try self.addDiag(.type_mismatch, token);
        return .poison;
    }
};

/// Run semantic analysis on a parsed AST.
pub fn analyze(allocator: std.mem.Allocator, tree: *const Ast) std.mem.Allocator.Error!Sema {
    const node_types = try allocator.alloc(Type, tree.nodes.len);
    errdefer allocator.free(node_types);

    var a = Analyzer{
        .tree = tree,
        .allocator = allocator,
        .symbols = std.StringArrayHashMap(Symbol).init(allocator),
        .node_types = node_types,
        .diagnostics = std.ArrayList(Diagnostic).empty,
    };
    errdefer a.symbols.deinit();
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
    try std.testing.expectEqual(.f64, sym.ty);
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
    try std.testing.expectEqual(.f64, sema.symbols.get("c").?.ty);
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
    try std.testing.expectEqual(.f64, sem.symbols.get("x").?.ty);
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
    try std.testing.expectEqual(.f64, sem.symbols.get("x").?.ty);
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
    try std.testing.expectEqual(.f64, sem.symbols.get("x").?.ty);
}

test "analyze: reference in arithmetic" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "let a = 2 let x = a * 3";

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    try std.testing.expect(!sem.hasErrors());
    try std.testing.expectEqual(.f64, sem.symbols.get("x").?.ty);
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

test "analyze: input resolves type" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "input head = 100mm";

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sema = try analyze(allocator, &tree);
    defer sema.deinit();

    try std.testing.expect(!sema.hasErrors());
    const sym = sema.symbols.get("head").?;
    try std.testing.expectEqual(.length, sym.ty);
    try std.testing.expectEqual(.input, sym.kind);
}

test "analyze: input referenced in let" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "input head = 100mm let x = head";

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sema = try analyze(allocator, &tree);
    defer sema.deinit();

    try std.testing.expect(!sema.hasErrors());
    try std.testing.expectEqual(.input, sema.symbols.get("head").?.kind);
    try std.testing.expectEqual(.let_binding, sema.symbols.get("x").?.kind);
    try std.testing.expectEqual(.length, sema.symbols.get("x").?.ty);
}

test "analyze: duplicate input" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "input head = 100mm input head = 200mm";

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sema = try analyze(allocator, &tree);
    defer sema.deinit();

    try std.testing.expect(sema.hasErrors());
    try std.testing.expectEqual(1, sema.diagnostics.len);
    try std.testing.expectEqual(.duplicate_binding, sema.diagnostics[0].tag);
}

test "analyze: duplicate name across input and let" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "input x = 100mm let x = 200mm";

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sema = try analyze(allocator, &tree);
    defer sema.deinit();

    try std.testing.expect(sema.hasErrors());
    try std.testing.expectEqual(1, sema.diagnostics.len);
    try std.testing.expectEqual(.duplicate_binding, sema.diagnostics[0].tag);
}

test "analyze: let bindings have let_binding kind" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "let x = 100mm";

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sema = try analyze(allocator, &tree);
    defer sema.deinit();

    try std.testing.expect(!sema.hasErrors());
    try std.testing.expectEqual(.let_binding, sema.symbols.get("x").?.kind);
}

test "analyze: point constructor resolves to point type" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "let p = point(100mm, 50mm)";

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    try std.testing.expect(!sem.hasErrors());
    try std.testing.expectEqual(.point, sem.symbols.get("p").?.ty);
}

test "analyze: point with ref args" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "input head = 100mm let p = point(head, 0mm)";

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    try std.testing.expect(!sem.hasErrors());
    try std.testing.expectEqual(.point, sem.symbols.get("p").?.ty);
}

test "analyze: point with expression args" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "let a = 100mm let p = point(a * 2, a / 3)";

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    try std.testing.expect(!sem.hasErrors());
    try std.testing.expectEqual(.point, sem.symbols.get("p").?.ty);
}

test "analyze: point rejects f64 args" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "let p = point(42, 50mm)";

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    try std.testing.expect(sem.hasErrors());
    try std.testing.expectEqual(.argument_type_mismatch, sem.diagnostics[0].tag);
}

test "analyze: point rejects wrong arg count" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "let p = point(100mm)";

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    try std.testing.expect(sem.hasErrors());
    try std.testing.expectEqual(.wrong_argument_count, sem.diagnostics[0].tag);
}

test "analyze: unknown function" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "let p = foo(100mm, 50mm)";

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    try std.testing.expect(sem.hasErrors());
    try std.testing.expectEqual(.unknown_function, sem.diagnostics[0].tag);
}

test "analyze: point poison propagation" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "let p = point(unknown, 50mm)";

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    // Only one error for the undefined ref, poison propagates through point.
    try std.testing.expectEqual(1, sem.diagnostics.len);
    try std.testing.expectEqual(.undefined_reference, sem.diagnostics[0].tag);
    try std.testing.expectEqual(.poison, sem.symbols.get("p").?.ty);
}

test "analyze: point in arithmetic is type mismatch" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "let p = point(100mm, 50mm) let x = p + 1";

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    try std.testing.expect(sem.hasErrors());
    try std.testing.expectEqual(.type_mismatch, sem.diagnostics[0].tag);
}

test "analyze: bezier constructor resolves to bezier type" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 =
        \\let p1 = point(0mm, 0mm)
        \\let p2 = point(100mm, 0mm)
        \\let p3 = point(100mm, 100mm)
        \\let p4 = point(0mm, 100mm)
        \\let c = bezier(p1, p2, p3, p4)
    ;

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    try std.testing.expect(!sem.hasErrors());
    try std.testing.expectEqual(.bezier, sem.symbols.get("c").?.ty);
}

test "analyze: bezier rejects non-point args" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 =
        \\let p1 = point(0mm, 0mm)
        \\let c = bezier(p1, p1, p1, 100mm)
    ;

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    try std.testing.expect(sem.hasErrors());
    try std.testing.expectEqual(.argument_type_mismatch, sem.diagnostics[0].tag);
}

test "analyze: bezier rejects wrong arg count" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 =
        \\let p1 = point(0mm, 0mm)
        \\let c = bezier(p1, p1, p1)
    ;

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    try std.testing.expect(sem.hasErrors());
    try std.testing.expectEqual(.wrong_argument_count, sem.diagnostics[0].tag);
}

test "analyze: bezier poison propagation" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 =
        \\let p1 = point(0mm, 0mm)
        \\let c = bezier(p1, p1, p1, unknown)
    ;

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    try std.testing.expectEqual(1, sem.diagnostics.len);
    try std.testing.expectEqual(.undefined_reference, sem.diagnostics[0].tag);
    try std.testing.expectEqual(.poison, sem.symbols.get("c").?.ty);
}

test "analyze: bezier in arithmetic is type mismatch" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 =
        \\let p1 = point(0mm, 0mm)
        \\let c = bezier(p1, p1, p1, p1)
        \\let x = c + 1
    ;

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    try std.testing.expect(sem.hasErrors());
    try std.testing.expectEqual(.type_mismatch, sem.diagnostics[0].tag);
}

test "analyze: line constructor resolves to line type" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 =
        \\let a = point(0mm, 0mm)
        \\let b = point(100mm, 50mm)
        \\let c = line(a, b)
    ;

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    try std.testing.expect(!sem.hasErrors());
    try std.testing.expectEqual(.line, sem.symbols.get("c").?.ty);
}

test "analyze: line rejects non-point args" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "let c = line(100mm, 50mm)";

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    try std.testing.expect(sem.hasErrors());
    try std.testing.expectEqual(.argument_type_mismatch, sem.diagnostics[0].tag);
}

test "analyze: line rejects wrong arg count" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 =
        \\let a = point(0mm, 0mm)
        \\let c = line(a)
    ;

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    try std.testing.expect(sem.hasErrors());
    try std.testing.expectEqual(.wrong_argument_count, sem.diagnostics[0].tag);
}

test "analyze: line poison propagation" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 =
        \\let a = point(0mm, 0mm)
        \\let c = line(a, unknown)
    ;

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    try std.testing.expectEqual(1, sem.diagnostics.len);
    try std.testing.expectEqual(.undefined_reference, sem.diagnostics[0].tag);
    try std.testing.expectEqual(.poison, sem.symbols.get("c").?.ty);
}

test "analyze: line in arithmetic is type mismatch" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 =
        \\let a = point(0mm, 0mm)
        \\let b = point(100mm, 50mm)
        \\let c = line(a, b)
        \\let x = c + 1
    ;

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    try std.testing.expect(sem.hasErrors());
    try std.testing.expectEqual(.type_mismatch, sem.diagnostics[0].tag);
}
