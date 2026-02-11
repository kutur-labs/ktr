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
    /// Named collection of member bindings.
    piece,
    /// Unresolvable value; suppresses cascading diagnostics.
    poison,
};

pub const Symbol = struct {
    ty: Type,
    /// AST node index of the defining statement (let_statement, input_statement, or fn_def for params).
    node: ast.NodeIndex,
    kind: Kind,

    pub const Kind = enum { let_binding, input, fn_param };
};

pub const ParamInfo = struct {
    name: []const u8,
    ty: Type,
};

pub const FnSig = struct {
    params: []const ParamInfo,
    ret_ty: Type,
    piece_info: ?PieceInfo = null,
    node: ast.NodeIndex,
};

pub const PieceMember = struct {
    name: []const u8,
    ty: Type,
};

pub const PieceInfo = struct {
    members: []const PieceMember,
};

fn deinitPieceMap(
    allocator: std.mem.Allocator,
    pieces: *std.StringArrayHashMap(PieceInfo),
) void {
    for (pieces.values()) |info| {
        allocator.free(info.members);
    }
    pieces.deinit();
}

fn deinitPieceExprInfoMap(
    allocator: std.mem.Allocator,
    piece_expr_infos: *std.AutoHashMap(ast.NodeIndex, PieceInfo),
) void {
    var it = piece_expr_infos.valueIterator();
    while (it.next()) |info| {
        allocator.free(info.members);
    }
    piece_expr_infos.deinit();
}

/// Result of semantic analysis. Symbol names are slices borrowed from the
/// original source buffer (via the Ast), so the caller must keep both the
/// source and the Ast alive for the lifetime of this Sema.
pub const Sema = struct {
    /// Ordered map of bindings in source order. The lowerer depends on
    /// iteration order matching definition order.
    symbols: std.StringArrayHashMap(Symbol),
    /// User-defined function signatures, keyed by function name.
    functions: std.StringArrayHashMap(FnSig),
    /// Top-level piece definitions, keyed by piece name.
    pieces: std.StringArrayHashMap(PieceInfo),
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
        for (self.functions.values()) |sig| {
            self.allocator.free(sig.params);
            if (sig.piece_info) |info| self.allocator.free(info.members);
        }
        self.functions.deinit();
        deinitPieceMap(self.allocator, &self.pieces);
        self.allocator.free(self.node_types);
        self.allocator.free(self.diagnostics);
        self.* = undefined;
    }
};

const Analyzer = struct {
    tree: *const Ast,
    allocator: std.mem.Allocator,
    symbols: std.StringArrayHashMap(Symbol),
    functions: std.StringArrayHashMap(FnSig),
    pieces: std.StringArrayHashMap(PieceInfo),
    piece_expr_infos: std.AutoHashMap(ast.NodeIndex, PieceInfo),
    node_types: []Type,
    diagnostics: std.ArrayList(Diagnostic),

    fn addDiag(self: *Analyzer, tag: Diagnostic.Tag, token: u32) std.mem.Allocator.Error!void {
        try self.diagnostics.append(self.allocator, .{ .tag = tag, .token = token });
    }

    /// Check if `name` exists in the local portion of the symbol table
    /// (entries at index >= `scope_start`). Used by function analysis to
    /// allow params/locals to shadow outer-scope bindings.
    fn containsLocal(self: *const Analyzer, name: []const u8, scope_start: usize) bool {
        const keys = self.symbols.keys();
        for (keys[scope_start..]) |k| {
            if (std.mem.eql(u8, k, name)) return true;
        }
        return false;
    }

    /// A lexical scope context that tracks the symbol table boundary and
    /// any outer-scope entries shadowed within this scope. On `restore()`,
    /// new entries are popped and shadowed entries are put back.
    const ScopedContext = struct {
        const SavedEntry = struct { name: []const u8, sym: Symbol };
        analyzer: *Analyzer,
        outer_count: usize,
        saved: std.ArrayList(SavedEntry),

        fn init(analyzer: *Analyzer) ScopedContext {
            return .{
                .analyzer = analyzer,
                .outer_count = analyzer.symbols.count(),
                .saved = std.ArrayList(SavedEntry).empty,
            };
        }

        /// Check if `name` already exists within this scope (not outer).
        fn containsLocal(self: *const ScopedContext, name: []const u8) bool {
            return self.analyzer.containsLocal(name, self.outer_count);
        }

        /// Put a symbol, saving any shadowed outer-scope entry for later restore.
        fn put(self: *ScopedContext, name: []const u8, sym: Symbol) std.mem.Allocator.Error!void {
            if (self.analyzer.symbols.getIndex(name)) |idx| {
                if (idx < self.outer_count) {
                    try self.saved.append(self.analyzer.allocator, .{
                        .name = name,
                        .sym = self.analyzer.symbols.values()[idx],
                    });
                }
            }
            try self.analyzer.symbols.put(name, sym);
        }

        /// Pop all scope-local entries and restore any shadowed outer entries.
        fn restore(self: *ScopedContext) std.mem.Allocator.Error!void {
            while (self.analyzer.symbols.count() > self.outer_count) {
                _ = self.analyzer.symbols.pop();
            }
            for (self.saved.items) |entry| {
                try self.analyzer.symbols.put(entry.name, entry.sym);
            }
        }

        fn deinit(self: *ScopedContext) void {
            self.saved.deinit(self.analyzer.allocator);
        }
    };

    fn analyzeRoot(self: *Analyzer) std.mem.Allocator.Error!void {
        const statements = self.tree.rootStatements(0);
        for (statements) |stmt_index| {
            const node = self.tree.nodes.get(stmt_index);
            switch (node.tag) {
                .let_statement => try self.analyzeBinding(node, stmt_index, .let_binding),
                .input_statement => try self.analyzeBinding(node, stmt_index, .input),
                .fn_def => try self.analyzeFnDef(node, stmt_index),
                .piece_def => try self.analyzePieceDef(node, stmt_index),
                else => {},
            }
        }
    }

    /// Parse a type name token text into a sema Type.
    fn parseTypeName(text: []const u8) ?Type {
        const type_map = std.StaticStringMap(Type).initComptime(.{
            .{ "f64", .f64 },
            .{ "length", .length },
            .{ "percentage", .percentage },
            .{ "point", .point },
            .{ "bezier", .bezier },
            .{ "line", .line },
            .{ "piece", .piece },
        });
        return type_map.get(text);
    }

    fn analyzePieceMembers(self: *Analyzer, member_nodes: []const ast.NodeIndex) std.mem.Allocator.Error![]const PieceMember {
        var scope = ScopedContext.init(self);
        defer scope.deinit();

        var member_infos = std.ArrayList(PieceMember).empty;
        defer member_infos.deinit(self.allocator);

        for (member_nodes) |member_idx| {
            const member_node = self.tree.nodes.get(member_idx);
            const member_name = self.tree.tokenSlice(member_node.main_token);

            // Members are in a lexical scope local to this piece.
            if (scope.containsLocal(member_name)) {
                try self.addDiag(.duplicate_binding, member_node.main_token);
                continue;
            }

            const member_ty = try self.resolveType(member_node.data.lhs);
            try scope.put(member_name, .{
                .ty = member_ty,
                .node = member_idx,
                .kind = .let_binding,
            });
            try member_infos.append(self.allocator, .{
                .name = member_name,
                .ty = member_ty,
            });
        }

        // Piece members do not leak to outer scope.
        try scope.restore();

        return member_infos.toOwnedSlice(self.allocator);
    }

    fn analyzePieceDef(self: *Analyzer, node: ast.Node, node_index: ast.NodeIndex) std.mem.Allocator.Error!void {
        const piece_name = self.tree.tokenSlice(node.main_token + 1);

        // Piece names share the top-level namespace with bindings and functions.
        if (self.symbols.contains(piece_name) or self.functions.contains(piece_name) or self.pieces.contains(piece_name)) {
            try self.addDiag(.duplicate_binding, node.main_token);
            return;
        }

        const member_nodes = self.tree.pieceDefMembers(node_index);
        const owned_members = try self.analyzePieceMembers(member_nodes);
        errdefer self.allocator.free(owned_members);

        try self.pieces.put(piece_name, .{
            .members = owned_members,
        });
        try self.symbols.put(piece_name, .{
            .ty = .piece,
            .node = node_index,
            .kind = .let_binding,
        });
    }

    fn analyzePieceExpr(self: *Analyzer, node_index: ast.NodeIndex) std.mem.Allocator.Error!void {
        if (self.piece_expr_infos.contains(node_index)) return;
        const member_nodes = self.tree.pieceExprMembers(node_index);
        const members = try self.analyzePieceMembers(member_nodes);
        errdefer self.allocator.free(members);
        try self.piece_expr_infos.put(node_index, .{
            .members = members,
        });
    }

    fn resolvePieceInfoFromSymbol(self: *const Analyzer, sym: Symbol, name: []const u8) ?*const PieceInfo {
        if (sym.ty != .piece) return null;
        const def_node = self.tree.nodes.get(sym.node);
        return switch (def_node.tag) {
            .piece_def => self.pieces.getPtr(name),
            .let_statement, .input_statement => self.resolvePieceInfo(def_node.data.lhs),
            else => null,
        };
    }

    fn resolvePieceInfo(self: *const Analyzer, node_index: ast.NodeIndex) ?*const PieceInfo {
        const node = self.tree.nodes.get(node_index);
        return switch (node.tag) {
            .identifier_ref => blk: {
                const name = self.tree.tokenSlice(node.main_token);
                if (self.pieces.getPtr(name)) |piece_info| break :blk piece_info;
                const sym = self.symbols.get(name) orelse break :blk null;
                break :blk self.resolvePieceInfoFromSymbol(sym, name);
            },
            .grouped_expression => self.resolvePieceInfo(node.data.lhs),
            .piece_expr => self.piece_expr_infos.getPtr(node_index),
            .fn_call => blk: {
                const fn_name = self.tree.tokenSlice(node.main_token);
                const fn_sig = self.functions.getPtr(fn_name) orelse break :blk null;
                if (fn_sig.ret_ty != .piece) break :blk null;
                if (fn_sig.piece_info) |*piece_info| break :blk piece_info;
                break :blk null;
            },
            else => null,
        };
    }

    fn analyzeFnDef(self: *Analyzer, node: ast.Node, node_index: ast.NodeIndex) std.mem.Allocator.Error!void {
        const fn_name = self.tree.tokenSlice(node.main_token + 1);

        // Check for duplicate name (against bindings and other functions).
        if (self.symbols.contains(fn_name) or self.functions.contains(fn_name)) {
            try self.addDiag(.duplicate_function, node.main_token);
            return;
        }

        const param_nodes = self.tree.fnDefParams(node_index);
        const body_nodes = self.tree.fnDefBody(node_index);
        const return_expr = self.tree.fnDefReturn(node_index);

        var scope = ScopedContext.init(self);
        defer scope.deinit();

        // Build param info and add params to symbol table temporarily.
        var params = try self.allocator.alloc(ParamInfo, param_nodes.len);

        for (param_nodes, 0..) |param_idx, i| {
            const param_node = self.tree.nodes.get(param_idx);
            const param_name = self.tree.tokenSlice(param_node.main_token);
            const type_text = self.tree.tokenSlice(@intCast(param_node.data.lhs));
            const param_ty = parseTypeName(type_text) orelse {
                try self.addDiag(.expected_type_name, @intCast(param_node.data.lhs));
                // Use poison to continue analysis.
                params[i] = .{ .name = param_name, .ty = .poison };
                continue;
            };

            params[i] = .{ .name = param_name, .ty = param_ty };

            // Check for duplicate within this function's scope only.
            // Params are allowed to shadow outer bindings.
            if (scope.containsLocal(param_name)) {
                try self.addDiag(.duplicate_binding, param_node.main_token);
                continue;
            }

            // Save any outer-scope entry being shadowed.
            try scope.put(param_name, .{ .ty = param_ty, .node = param_idx, .kind = .fn_param });
        }

        // Analyze body let-statements.
        for (body_nodes) |stmt_idx| {
            const stmt_node = self.tree.nodes.get(stmt_idx);
            if (stmt_node.tag == .let_statement) {
                try self.analyzeFnBinding(stmt_node, stmt_idx, &scope);
            }
        }

        // Analyze return expression and infer return type.
        const ret_ty = try self.resolveType(return_expr);
        var ret_piece_info: ?PieceInfo = null;
        if (ret_ty == .piece) {
            if (self.resolvePieceInfo(return_expr)) |piece_info| {
                ret_piece_info = .{
                    .members = try self.allocator.dupe(PieceMember, piece_info.members),
                };
            }
        }

        try scope.restore();

        // Register the function signature.
        try self.functions.put(fn_name, .{
            .params = params,
            .ret_ty = ret_ty,
            .piece_info = ret_piece_info,
            .node = node_index,
        });
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

    /// Like `analyzeBinding`, but only checks for duplicates within the
    /// function's local scope. Allows function-local bindings to shadow
    /// outer-scope names.
    fn analyzeFnBinding(self: *Analyzer, node: ast.Node, node_index: ast.NodeIndex, scope: *ScopedContext) std.mem.Allocator.Error!void {
        const name = self.tree.tokenSlice(node.main_token + 1);

        if (scope.containsLocal(name)) {
            try self.addDiag(.duplicate_binding, node.main_token);
            return;
        }

        const ty = try self.resolveType(node.data.lhs);

        try scope.put(name, .{ .ty = ty, .node = node_index, .kind = .let_binding });
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
            .field_access => blk2: {
                const base_ty = try self.resolveType(node.data.lhs);
                if (base_ty == .poison) break :blk2 .poison;
                const field_name = self.tree.tokenSlice(node.main_token + 1);
                if (base_ty == .piece) {
                    const piece_info = self.resolvePieceInfo(node.data.lhs) orelse {
                        try self.addDiag(.invalid_field_access, node.main_token + 1);
                        break :blk2 .poison;
                    };
                    for (piece_info.members) |member| {
                        if (std.mem.eql(u8, member.name, field_name)) {
                            break :blk2 member.ty;
                        }
                    }
                    try self.addDiag(.invalid_field_access, node.main_token + 1);
                    break :blk2 .poison;
                }
                // Map sema type to ir type for non-piece field lookups.
                const ir_base_ty = std.meta.stringToEnum(ir.Type, @tagName(base_ty)) orelse {
                    try self.addDiag(.invalid_field_access, node.main_token + 1);
                    break :blk2 .poison;
                };
                if (ir.lookupField(ir_base_ty, field_name)) |info| {
                    break :blk2 mapFromIrType(info.result_ty);
                }
                try self.addDiag(.invalid_field_access, node.main_token + 1);
                break :blk2 .poison;
            },
            .piece_expr => blk3: {
                try self.analyzePieceExpr(node_index);
                break :blk3 .piece;
            },
            // Structurally impossible: the parser only produces expression nodes
            // as values in statements; non-expression nodes never appear here.
            .root, .let_statement, .input_statement, .fn_def, .piece_def, .piece_member, .param, .return_stmt => unreachable,
        };
        self.node_types[node_index] = ty;
        return ty;
    }

    fn resolveCallType(self: *Analyzer, node_index: ast.NodeIndex) std.mem.Allocator.Error!Type {
        const node = self.tree.nodes.get(node_index);
        const name = self.tree.tokenSlice(node.main_token);
        const args = self.tree.callArgs(node_index);

        // Look up in the centralized builtin registry (ir.zig) first.
        if (ir.builtin_sigs.get(name)) |sig| {
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

        // Check user-defined functions.
        if (self.functions.get(name)) |fn_sig| {
            // Check argument count.
            if (args.len != fn_sig.params.len) {
                try self.addDiag(.wrong_argument_count, node.main_token);
                return .poison;
            }

            // Check each argument type.
            var has_poison = false;
            for (args, fn_sig.params) |arg_idx, param_info| {
                const actual_ty = try self.resolveType(arg_idx);
                if (actual_ty == .poison) {
                    has_poison = true;
                    continue;
                }
                if (actual_ty != param_info.ty) {
                    try self.addDiag(.argument_type_mismatch, self.tree.nodes.items(.main_token)[arg_idx]);
                }
            }

            if (has_poison) return .poison;
            return fn_sig.ret_ty;
        }

        try self.addDiag(.unknown_function, node.main_token);
        return .poison;
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
        .functions = std.StringArrayHashMap(FnSig).init(allocator),
        .pieces = std.StringArrayHashMap(PieceInfo).init(allocator),
        .piece_expr_infos = std.AutoHashMap(ast.NodeIndex, PieceInfo).init(allocator),
        .node_types = node_types,
        .diagnostics = std.ArrayList(Diagnostic).empty,
    };
    errdefer a.symbols.deinit();
    errdefer a.functions.deinit();
    errdefer deinitPieceMap(allocator, &a.pieces);
    errdefer deinitPieceExprInfoMap(allocator, &a.piece_expr_infos);
    errdefer a.diagnostics.deinit(allocator);

    try a.analyzeRoot();

    // Temporary piece-expression shape cache is only needed during analysis.
    deinitPieceExprInfoMap(allocator, &a.piece_expr_infos);

    return .{
        .symbols = a.symbols,
        .functions = a.functions,
        .pieces = a.pieces,
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

test "analyze: fn_def simple" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "fn double(x: f64) { return x * 2 }";

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    try std.testing.expect(!sem.hasErrors());
    try std.testing.expectEqual(1, sem.functions.count());
    const sig = sem.functions.get("double").?;
    try std.testing.expectEqual(.f64, sig.ret_ty);
    try std.testing.expectEqual(1, sig.params.len);
    try std.testing.expectEqualStrings("x", sig.params[0].name);
    try std.testing.expectEqual(.f64, sig.params[0].ty);
}

test "analyze: fn_def with length params" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "fn add(a: length, b: length) { return a + b }";

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    try std.testing.expect(!sem.hasErrors());
    const sig = sem.functions.get("add").?;
    try std.testing.expectEqual(.length, sig.ret_ty);
    try std.testing.expectEqual(2, sig.params.len);
}

test "analyze: fn_def with body" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 =
        \\fn half(x: length) {
        \\  let result = x / 2
        \\  return result
        \\}
    ;

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    try std.testing.expect(!sem.hasErrors());
    const sig = sem.functions.get("half").?;
    try std.testing.expectEqual(.length, sig.ret_ty);
}

test "analyze: fn_def params don't leak into outer scope" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 =
        \\fn double(x: f64) { return x * 2 }
        \\let y = x
    ;

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    try std.testing.expect(sem.hasErrors());
    try std.testing.expectEqual(.undefined_reference, sem.diagnostics[0].tag);
}

test "analyze: fn_def body locals don't leak" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 =
        \\fn foo(x: f64) {
        \\  let temp = x * 2
        \\  return temp
        \\}
        \\let y = temp
    ;

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    try std.testing.expect(sem.hasErrors());
    try std.testing.expectEqual(.undefined_reference, sem.diagnostics[0].tag);
}

test "analyze: fn call user-defined" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 =
        \\fn double(x: f64) { return x * 2 }
        \\let y = double(5)
    ;

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    try std.testing.expect(!sem.hasErrors());
    try std.testing.expectEqual(.f64, sem.symbols.get("y").?.ty);
}

test "analyze: fn call wrong arg count" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 =
        \\fn double(x: f64) { return x * 2 }
        \\let y = double(1, 2)
    ;

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    try std.testing.expect(sem.hasErrors());
    try std.testing.expectEqual(.wrong_argument_count, sem.diagnostics[0].tag);
}

test "analyze: fn call wrong arg type" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 =
        \\fn half(x: length) { return x / 2 }
        \\let y = half(42)
    ;

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    try std.testing.expect(sem.hasErrors());
    try std.testing.expectEqual(.argument_type_mismatch, sem.diagnostics[0].tag);
}

test "analyze: duplicate function name" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 =
        \\fn foo(x: f64) { return x }
        \\fn foo(y: f64) { return y }
    ;

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    try std.testing.expect(sem.hasErrors());
    try std.testing.expectEqual(.duplicate_function, sem.diagnostics[0].tag);
}

test "analyze: fn name conflicts with binding" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 =
        \\let foo = 42
        \\fn foo(x: f64) { return x }
    ;

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    try std.testing.expect(sem.hasErrors());
    try std.testing.expectEqual(.duplicate_function, sem.diagnostics[0].tag);
}

test "analyze: fn references outer input" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 =
        \\input head = 100mm
        \\fn scale_head(factor: f64) { return head * factor }
        \\let y = scale_head(2)
    ;

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    try std.testing.expect(!sem.hasErrors());
    try std.testing.expectEqual(.length, sem.functions.get("scale_head").?.ret_ty);
    try std.testing.expectEqual(.length, sem.symbols.get("y").?.ty);
}

test "analyze: fn returns point" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 =
        \\fn origin() { return point(0mm, 0mm) }
        \\let p = origin()
    ;

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    try std.testing.expect(!sem.hasErrors());
    try std.testing.expectEqual(.point, sem.functions.get("origin").?.ret_ty);
    try std.testing.expectEqual(.point, sem.symbols.get("p").?.ty);
}

test "analyze: fn param shadows outer binding" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 =
        \\input head = 100mm
        \\fn scale(head: f64) { return head * 2 }
        \\let y = scale(3)
    ;

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    // Param `head` shadows the outer input -- no error.
    try std.testing.expect(!sem.hasErrors());
    try std.testing.expectEqual(.f64, sem.functions.get("scale").?.ret_ty);
    try std.testing.expectEqual(.f64, sem.symbols.get("y").?.ty);
}

test "analyze: fn body local shadows outer binding" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 =
        \\let x = 100mm
        \\fn foo(a: f64) {
        \\  let x = a * 2
        \\  return x
        \\}
        \\let y = foo(3)
    ;

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    // Body local `x` shadows the outer let -- no error.
    try std.testing.expect(!sem.hasErrors());
    try std.testing.expectEqual(.f64, sem.functions.get("foo").?.ret_ty);
    try std.testing.expectEqual(.f64, sem.symbols.get("y").?.ty);
}

test "analyze: fn duplicate param within function" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 =
        \\fn foo(x: f64, x: f64) { return x }
    ;

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    // Duplicate param within the same function is still an error.
    try std.testing.expect(sem.hasErrors());
    try std.testing.expectEqual(.duplicate_binding, sem.diagnostics[0].tag);
}

test "analyze: point.x resolves to length" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "let p = point(100mm, 50mm) let x = p.x";

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    try std.testing.expect(!sem.hasErrors());
    try std.testing.expectEqual(.length, sem.symbols.get("x").?.ty);
}

test "analyze: point.y resolves to length" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "let p = point(100mm, 50mm) let y = p.y";

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    try std.testing.expect(!sem.hasErrors());
    try std.testing.expectEqual(.length, sem.symbols.get("y").?.ty);
}

test "analyze: line.point1 resolves to point" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 =
        \\let a = point(0mm, 0mm)
        \\let b = point(100mm, 50mm)
        \\let l = line(a, b)
        \\let p = l.point1
    ;

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    try std.testing.expect(!sem.hasErrors());
    try std.testing.expectEqual(.point, sem.symbols.get("p").?.ty);
}

test "analyze: line.point2 resolves to point" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 =
        \\let a = point(0mm, 0mm)
        \\let b = point(100mm, 50mm)
        \\let l = line(a, b)
        \\let p = l.point2
    ;

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    try std.testing.expect(!sem.hasErrors());
    try std.testing.expectEqual(.point, sem.symbols.get("p").?.ty);
}

test "analyze: bezier.point1 resolves to point" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 =
        \\let p1 = point(0mm, 0mm)
        \\let p2 = point(100mm, 0mm)
        \\let p3 = point(100mm, 100mm)
        \\let p4 = point(0mm, 100mm)
        \\let c = bezier(p1, p2, p3, p4)
        \\let q = c.point1
    ;

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    try std.testing.expect(!sem.hasErrors());
    try std.testing.expectEqual(.point, sem.symbols.get("q").?.ty);
}

test "analyze: chained field access line.point1.x resolves to length" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 =
        \\let a = point(0mm, 0mm)
        \\let b = point(100mm, 50mm)
        \\let l = line(a, b)
        \\let x = l.point1.x
    ;

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    try std.testing.expect(!sem.hasErrors());
    try std.testing.expectEqual(.length, sem.symbols.get("x").?.ty);
}

test "analyze: invalid field on point" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "let p = point(100mm, 50mm) let z = p.z";

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    try std.testing.expect(sem.hasErrors());
    try std.testing.expectEqual(.invalid_field_access, sem.diagnostics[0].tag);
}

test "analyze: field access on scalar type" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "let x = 42 let y = x.foo";

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    try std.testing.expect(sem.hasErrors());
    try std.testing.expectEqual(.invalid_field_access, sem.diagnostics[0].tag);
}

test "analyze: field access poison propagation" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "let y = unknown.x";

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    // One error for undefined ref, poison propagates through field access.
    try std.testing.expectEqual(1, sem.diagnostics.len);
    try std.testing.expectEqual(.undefined_reference, sem.diagnostics[0].tag);
    try std.testing.expectEqual(.poison, sem.symbols.get("y").?.ty);
}

test "analyze: field access result usable in arithmetic" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "let p = point(100mm, 50mm) let x = p.x * 2";

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    try std.testing.expect(!sem.hasErrors());
    try std.testing.expectEqual(.length, sem.symbols.get("x").?.ty);
}

test "analyze: piece definition registers piece info" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 =
        \\input chest = 100mm
        \\piece neckhole {
        \\  top_left = point(chest, 0mm)
        \\  top_right = point(chest, top_left.y)
        \\}
    ;

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    try std.testing.expect(!sem.hasErrors());
    try std.testing.expectEqual(.piece, sem.symbols.get("neckhole").?.ty);

    const info = sem.pieces.get("neckhole").?;
    try std.testing.expectEqual(@as(usize, 2), info.members.len);
    try std.testing.expectEqualStrings("top_left", info.members[0].name);
    try std.testing.expectEqual(.point, info.members[0].ty);
    try std.testing.expectEqualStrings("top_right", info.members[1].name);
    try std.testing.expectEqual(.point, info.members[1].ty);
}

test "analyze: piece members are visible in definition order" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 =
        \\piece neckhole {
        \\  top_right = point(top_left.x, 0mm)
        \\  top_left = point(100mm, 50mm)
        \\}
    ;

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    try std.testing.expect(sem.hasErrors());
    try std.testing.expectEqual(@as(usize, 1), sem.diagnostics.len);
    try std.testing.expectEqual(.undefined_reference, sem.diagnostics[0].tag);
}

test "analyze: piece members do not leak into outer scope" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 =
        \\piece neckhole {
        \\  top_left = point(0mm, 0mm)
        \\}
        \\let x = top_left
    ;

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    try std.testing.expect(sem.hasErrors());
    try std.testing.expectEqual(.undefined_reference, sem.diagnostics[0].tag);
}

test "analyze: piece member access resolves to member type" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 =
        \\piece neckhole {
        \\  top_left = point(100mm, 50mm)
        \\}
        \\let x = neckhole.top_left.x
    ;

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    try std.testing.expect(!sem.hasErrors());
    try std.testing.expectEqual(.length, sem.symbols.get("x").?.ty);
}

test "analyze: invalid piece member access" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 =
        \\piece neckhole {
        \\  top_left = point(100mm, 50mm)
        \\}
        \\let x = neckhole.missing
    ;

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    try std.testing.expect(sem.hasErrors());
    try std.testing.expectEqual(.invalid_field_access, sem.diagnostics[0].tag);
}

test "analyze: fn returning anonymous piece infers piece signature" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 =
        \\fn make_piece() {
        \\  return piece {
        \\    top_left = point(0mm, 0mm)
        \\  }
        \\}
        \\let x = make_piece().top_left.x
    ;

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    try std.testing.expect(!sem.hasErrors());
    const sig = sem.functions.get("make_piece").?;
    try std.testing.expectEqual(.piece, sig.ret_ty);
    try std.testing.expect(sig.piece_info != null);
    try std.testing.expectEqual(@as(usize, 1), sig.piece_info.?.members.len);
    try std.testing.expectEqualStrings("top_left", sig.piece_info.?.members[0].name);
    try std.testing.expectEqual(.point, sig.piece_info.?.members[0].ty);
    try std.testing.expectEqual(.length, sem.symbols.get("x").?.ty);
}

test "analyze: piece member access on piece-valued let from call" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 =
        \\fn make_piece() {
        \\  return piece {
        \\    top_left = point(0mm, 0mm)
        \\  }
        \\}
        \\let sleeve = make_piece()
        \\let y = sleeve.top_left.y
    ;

    var tree = try parser.parse(allocator, source);
    defer tree.deinit();

    var sem = try analyze(allocator, &tree);
    defer sem.deinit();

    try std.testing.expect(!sem.hasErrors());
    try std.testing.expectEqual(.piece, sem.symbols.get("sleeve").?.ty);
    try std.testing.expectEqual(.length, sem.symbols.get("y").?.ty);
}
