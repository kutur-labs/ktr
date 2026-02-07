const std = @import("std");
const lexer = @import("lexer.zig");
const ast = @import("ast.zig");
const Ast = ast.Ast;
const Diagnostic = ast.Diagnostic;

const Parser = struct {
    allocator: std.mem.Allocator,
    tokens: ast.TokenList,
    nodes: ast.NodeList,
    extra_data: std.ArrayList(u32),
    diagnostics: std.ArrayList(Diagnostic),
    cursor: ast.TokenIndex,

    /// Internal error: ParseFailed is used for recovery flow control,
    /// Allocator.Error propagates OOM.
    const Error = error{ParseFailed} || std.mem.Allocator.Error;

    fn addDiag(self: *Parser, tag: Diagnostic.Tag) std.mem.Allocator.Error!void {
        try self.diagnostics.append(self.allocator, .{ .tag = tag, .token = self.cursor });
    }

    fn currentTag(self: *const Parser) lexer.Token.Tag {
        if (self.cursor >= self.tokens.len) return .eof;
        return self.tokens.items(.tag)[self.cursor];
    }

    fn advance(self: *Parser) void {
        if (self.cursor < self.tokens.len) self.cursor += 1;
    }

    fn expect(self: *Parser, tag: lexer.Token.Tag, diag: Diagnostic.Tag) Error!ast.TokenIndex {
        if (self.currentTag() != tag) {
            try self.addDiag(diag);
            return error.ParseFailed;
        }
        const idx = self.cursor;
        self.advance();
        return idx;
    }

    fn addNode(self: *Parser, node: ast.Node) std.mem.Allocator.Error!ast.NodeIndex {
        const idx: ast.NodeIndex = @intCast(self.nodes.len);
        try self.nodes.append(self.allocator, node);
        return idx;
    }

    fn parseExpression(self: *Parser) Error!ast.NodeIndex {
        const tag = self.currentTag();
        const node_tag: ast.Node.Tag = switch (tag) {
            .identifier => .identifier_ref,
            .number_literal => .number_literal,
            .dimension_literal => .dimension_literal,
            .percentage_literal => .percentage_literal,
            else => {
                try self.addDiag(.expected_expression);
                return error.ParseFailed;
            },
        };
        const token = self.cursor;
        self.advance();
        return self.addNode(.{
            .tag = node_tag,
            .main_token = token,
            .data = .{ .lhs = 0, .rhs = 0 },
        });
    }

    fn parseLetStatement(self: *Parser) Error!ast.NodeIndex {
        const let_token = self.cursor;
        self.advance();
        _ = try self.expect(.identifier, .expected_identifier);
        _ = try self.expect(.equal, .expected_equal);
        const value_node = try self.parseExpression();

        return self.addNode(.{
            .tag = .let_statement,
            .main_token = let_token,
            .data = .{ .lhs = value_node, .rhs = 0 },
        });
    }

    fn parseStatement(self: *Parser) Error!ast.NodeIndex {
        return switch (self.currentTag()) {
            .let => self.parseLetStatement(),
            else => {
                try self.addDiag(.unexpected_token);
                return error.ParseFailed;
            },
        };
    }

    /// Skip tokens until a potential statement boundary is found.
    fn synchronize(self: *Parser) void {
        while (self.currentTag() != .eof) {
            if (self.currentTag() == .let) return;
            self.advance();
        }
    }

    fn parseRoot(self: *Parser) std.mem.Allocator.Error!ast.NodeIndex {
        const root_index = try self.addNode(.{
            .tag = .root,
            .main_token = 0,
            .data = .{ .lhs = 0, .rhs = 0 },
        });

        const start_extra = self.extra_data.items.len;
        while (self.currentTag() != .eof) {
            const stmt = self.parseStatement() catch |err| switch (err) {
                error.ParseFailed => {
                    self.synchronize();
                    continue;
                },
                else => |oom| return oom,
            };
            try self.extra_data.append(self.allocator, stmt);
        }
        const end_extra = self.extra_data.items.len;

        self.nodes.items(.data)[root_index] = .{
            .lhs = @intCast(start_extra),
            .rhs = @intCast(end_extra),
        };
        return root_index;
    }
};

/// Parse source into an AST. Caller owns the returned Ast and must call deinit().
pub fn parse(allocator: std.mem.Allocator, source: [:0]const u8) std.mem.Allocator.Error!Ast {
    var token_list = ast.TokenList{};
    errdefer token_list.deinit(allocator);

    var lex = lexer.Lexer.init(source);
    while (true) {
        const tok = lex.next();
        try token_list.append(allocator, tok);
        if (tok.tag == .eof) break;
    }

    var p = Parser{
        .allocator = allocator,
        .tokens = token_list,
        .nodes = ast.NodeList{},
        .extra_data = std.ArrayList(u32).empty,
        .diagnostics = std.ArrayList(Diagnostic).empty,
        .cursor = 0,
    };
    errdefer p.nodes.deinit(allocator);
    errdefer p.extra_data.deinit(allocator);
    errdefer p.diagnostics.deinit(allocator);

    _ = try p.parseRoot();

    const extra_slice = try p.extra_data.toOwnedSlice(allocator);
    errdefer allocator.free(extra_slice);
    const diag_slice = try p.diagnostics.toOwnedSlice(allocator);

    return .{
        .source = source,
        .tokens = p.tokens,
        .nodes = p.nodes,
        .extra_data = extra_slice,
        .diagnostics = diag_slice,
        .allocator = allocator,
    };
}

// --- Tests ---

test "parse: let x = 100mm" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "let x = 100mm";

    var tree = try parse(allocator, source);
    defer tree.deinit();

    try std.testing.expect(!tree.hasErrors());
    try std.testing.expectEqual(3, tree.nodes.len);
    const statements = tree.rootStatements(0);
    try std.testing.expectEqual(1, statements.len);

    const let_node = tree.nodes.get(statements[0]);
    try std.testing.expectEqual(.let_statement, let_node.tag);
    try std.testing.expectEqualStrings("x", tree.tokenSlice(let_node.main_token + 1));

    const value_node = tree.nodes.get(let_node.data.lhs);
    try std.testing.expectEqual(.dimension_literal, value_node.tag);
    try std.testing.expectEqualStrings("100mm", tree.tokenSlice(value_node.main_token));
}

test "parse: let y = 50%" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "let y = 50%";

    var tree = try parse(allocator, source);
    defer tree.deinit();

    try std.testing.expect(!tree.hasErrors());
    const statements = tree.rootStatements(0);
    const let_node = tree.nodes.get(statements[0]);
    const value_node = tree.nodes.get(let_node.data.lhs);
    try std.testing.expectEqual(.percentage_literal, value_node.tag);
    try std.testing.expectEqualStrings("50%", tree.tokenSlice(value_node.main_token));
}

test "parse: let x = 100 (unitless)" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "let x = 100";

    var tree = try parse(allocator, source);
    defer tree.deinit();

    try std.testing.expect(!tree.hasErrors());
    const statements = tree.rootStatements(0);
    const let_node = tree.nodes.get(statements[0]);
    const value_node = tree.nodes.get(let_node.data.lhs);
    try std.testing.expectEqual(.number_literal, value_node.tag);
    try std.testing.expectEqualStrings("100", tree.tokenSlice(value_node.main_token));
}

test "parse: invalid placement emits diagnostic" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "x let = 100mm";

    var tree = try parse(allocator, source);
    defer tree.deinit();

    try std.testing.expect(tree.hasErrors());
    try std.testing.expect(tree.diagnostics.len >= 1);
    try std.testing.expectEqual(.unexpected_token, tree.diagnostics[0].tag);
    try std.testing.expectEqual(0, tree.diagnostics[0].token);
}

test "parse: let y = x (identifier ref)" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "let y = x";

    var tree = try parse(allocator, source);
    defer tree.deinit();

    try std.testing.expect(!tree.hasErrors());
    const statements = tree.rootStatements(0);
    try std.testing.expectEqual(1, statements.len);

    const let_node = tree.nodes.get(statements[0]);
    try std.testing.expectEqual(.let_statement, let_node.tag);
    try std.testing.expectEqualStrings("y", tree.tokenSlice(let_node.main_token + 1));

    const value_node = tree.nodes.get(let_node.data.lhs);
    try std.testing.expectEqual(.identifier_ref, value_node.tag);
    try std.testing.expectEqualStrings("x", tree.tokenSlice(value_node.main_token));
}
