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
        return self.parseAdditiveExpr();
    }

    fn parseAdditiveExpr(self: *Parser) Error!ast.NodeIndex {
        var lhs = try self.parseMultiplicativeExpr();

        while (true) {
            const tag = self.currentTag();
            const node_tag: ast.Node.Tag = switch (tag) {
                .plus => .add,
                .minus => .sub,
                else => break,
            };
            const op_token = self.cursor;
            self.advance();
            const rhs = try self.parseMultiplicativeExpr();
            lhs = try self.addNode(.{
                .tag = node_tag,
                .main_token = op_token,
                .data = .{ .lhs = lhs, .rhs = rhs },
            });
        }

        return lhs;
    }

    fn parseMultiplicativeExpr(self: *Parser) Error!ast.NodeIndex {
        var lhs = try self.parsePrimaryExpr();

        while (true) {
            const tag = self.currentTag();
            const node_tag: ast.Node.Tag = switch (tag) {
                .star => .mul,
                .slash => .div,
                else => break,
            };
            const op_token = self.cursor;
            self.advance();
            const rhs = try self.parsePrimaryExpr();
            lhs = try self.addNode(.{
                .tag = node_tag,
                .main_token = op_token,
                .data = .{ .lhs = lhs, .rhs = rhs },
            });
        }

        return lhs;
    }

    fn peekTag(self: *const Parser) lexer.Token.Tag {
        const next = self.cursor + 1;
        if (next >= self.tokens.len) return .eof;
        return self.tokens.items(.tag)[next];
    }

    fn parsePrimaryExpr(self: *Parser) Error!ast.NodeIndex {
        const tag = self.currentTag();

        // Parenthesized grouping: '(' expression ')'
        if (tag == .l_paren) {
            const paren_token = self.cursor;
            self.advance();
            const inner = try self.parseExpression();
            _ = try self.expect(.r_paren, .expected_r_paren);
            return self.addNode(.{
                .tag = .grouped_expression,
                .main_token = paren_token,
                .data = .{ .lhs = inner, .rhs = 0 },
            });
        }

        // Function call: identifier '(' arg_list ')'
        if (tag == .identifier and self.peekTag() == .l_paren) {
            return self.parseFnCall();
        }

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

    fn parseFnCall(self: *Parser) Error!ast.NodeIndex {
        const name_token = self.cursor;
        self.advance(); // consume identifier
        self.advance(); // consume '('

        const start_extra = self.extra_data.items.len;

        // Parse comma-separated argument list.
        if (self.currentTag() != .r_paren) {
            const first_arg = try self.parseExpression();
            try self.extra_data.append(self.allocator, first_arg);

            while (self.currentTag() == .comma) {
                self.advance(); // consume ','
                const arg = try self.parseExpression();
                try self.extra_data.append(self.allocator, arg);
            }
        }

        _ = try self.expect(.r_paren, .expected_r_paren);
        const end_extra = self.extra_data.items.len;

        return self.addNode(.{
            .tag = .fn_call,
            .main_token = name_token,
            .data = .{ .lhs = @intCast(start_extra), .rhs = @intCast(end_extra) },
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

    fn parseInputStatement(self: *Parser) Error!ast.NodeIndex {
        const input_token = self.cursor;
        self.advance();
        _ = try self.expect(.identifier, .expected_identifier);
        _ = try self.expect(.equal, .expected_equal);

        // Input defaults must be a single literal value (not an expression).
        const value_node = try self.parseLiteral();

        return self.addNode(.{
            .tag = .input_statement,
            .main_token = input_token,
            .data = .{ .lhs = value_node, .rhs = 0 },
        });
    }

    /// Parse a single literal token: dimension, percentage, or number.
    fn parseLiteral(self: *Parser) Error!ast.NodeIndex {
        const node_tag: ast.Node.Tag = switch (self.currentTag()) {
            .dimension_literal => .dimension_literal,
            .percentage_literal => .percentage_literal,
            .number_literal => .number_literal,
            else => {
                try self.addDiag(.expected_literal);
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

    /// Parse a single typed parameter: `IDENT : type_name`.
    fn parseParam(self: *Parser) Error!ast.NodeIndex {
        const name_token = try self.expect(.identifier, .expected_identifier);
        _ = try self.expect(.colon, .expected_colon);

        // The type name is an identifier token whose text must match a known type.
        if (self.currentTag() != .identifier) {
            try self.addDiag(.expected_type_name);
            return error.ParseFailed;
        }
        const type_token = self.cursor;
        self.advance();

        return self.addNode(.{
            .tag = .param,
            .main_token = name_token,
            .data = .{ .lhs = type_token, .rhs = 0 },
        });
    }

    /// Parse a function definition: `fn IDENT ( [param_list] ) { fn_body }`.
    /// fn_body = { let_statement } return expression.
    fn parseFnDef(self: *Parser) Error!ast.NodeIndex {
        const fn_token = self.cursor;
        self.advance(); // consume 'fn'
        _ = try self.expect(.identifier, .expected_identifier);
        _ = try self.expect(.l_paren, .expected_r_paren); // reusing r_paren diag for lparen is ok for now

        // Collect fn_def content into a temporary buffer to avoid interleaving
        // with extra_data from nested expressions.
        var fn_extra = std.ArrayList(u32).empty;
        defer fn_extra.deinit(self.allocator);

        // Reserve slot for param_count.
        try fn_extra.append(self.allocator, 0);

        // Parse comma-separated parameter list.
        var param_count: u32 = 0;
        if (self.currentTag() != .r_paren) {
            const first_param = try self.parseParam();
            try fn_extra.append(self.allocator, first_param);
            param_count += 1;

            while (self.currentTag() == .comma) {
                self.advance(); // consume ','
                const p = try self.parseParam();
                try fn_extra.append(self.allocator, p);
                param_count += 1;
            }
        }
        fn_extra.items[0] = param_count;

        _ = try self.expect(.r_paren, .expected_r_paren);
        _ = try self.expect(.l_brace, .expected_l_brace);

        // Parse body: zero or more let statements followed by a return statement.
        while (self.currentTag() == .let) {
            const let_stmt = try self.parseLetStatement();
            try fn_extra.append(self.allocator, let_stmt);
        }

        // Expect return statement.
        if (self.currentTag() != .@"return") {
            try self.addDiag(.expected_return);
            return error.ParseFailed;
        }
        self.advance(); // consume 'return'
        const return_expr = try self.parseExpression();
        try fn_extra.append(self.allocator, return_expr);

        _ = try self.expect(.r_brace, .expected_r_brace);

        // Write collected extra data.
        const start_extra = self.extra_data.items.len;
        try self.extra_data.appendSlice(self.allocator, fn_extra.items);
        const end_extra = self.extra_data.items.len;

        return self.addNode(.{
            .tag = .fn_def,
            .main_token = fn_token,
            .data = .{ .lhs = @intCast(start_extra), .rhs = @intCast(end_extra) },
        });
    }

    fn parseStatement(self: *Parser) Error!ast.NodeIndex {
        return switch (self.currentTag()) {
            .let => self.parseLetStatement(),
            .input => self.parseInputStatement(),
            .@"fn" => self.parseFnDef(),
            else => {
                try self.addDiag(.unexpected_token);
                return error.ParseFailed;
            },
        };
    }

    /// Skip tokens until a potential statement boundary is found.
    fn synchronize(self: *Parser) void {
        while (self.currentTag() != .eof) {
            const tag = self.currentTag();
            if (tag == .let or tag == .input or tag == .@"fn") return;
            self.advance();
        }
    }

    fn parseRoot(self: *Parser) std.mem.Allocator.Error!ast.NodeIndex {
        const root_index = try self.addNode(.{
            .tag = .root,
            .main_token = 0,
            .data = .{ .lhs = 0, .rhs = 0 },
        });

        // Collect statement indices separately, then append them to
        // extra_data at the end. This avoids interleaving with fn_call
        // arguments that are also written to extra_data during parsing.
        var stmt_indices = std.ArrayList(u32).empty;
        defer stmt_indices.deinit(self.allocator);

        while (self.currentTag() != .eof) {
            const stmt = self.parseStatement() catch |err| switch (err) {
                error.ParseFailed => {
                    self.synchronize();
                    continue;
                },
                else => |oom| return oom,
            };
            try stmt_indices.append(self.allocator, stmt);
        }

        const start_extra = self.extra_data.items.len;
        try self.extra_data.appendSlice(self.allocator, stmt_indices.items);
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

test "parse: let x = a * 2" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "let x = a * 2";

    var tree = try parse(allocator, source);
    defer tree.deinit();

    try std.testing.expect(!tree.hasErrors());
    const statements = tree.rootStatements(0);
    try std.testing.expectEqual(1, statements.len);

    const let_node = tree.nodes.get(statements[0]);
    const value_node = tree.nodes.get(let_node.data.lhs);
    try std.testing.expectEqual(.mul, value_node.tag);

    // LHS of mul should be identifier_ref 'a'
    const lhs = tree.nodes.get(value_node.data.lhs);
    try std.testing.expectEqual(.identifier_ref, lhs.tag);
    try std.testing.expectEqualStrings("a", tree.tokenSlice(lhs.main_token));

    // RHS of mul should be number_literal '2'
    const rhs = tree.nodes.get(value_node.data.rhs);
    try std.testing.expectEqual(.number_literal, rhs.tag);
    try std.testing.expectEqualStrings("2", tree.tokenSlice(rhs.main_token));
}

test "parse: let x = (2 + 2) / 2" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "let x = (2 + 2) / 2";

    var tree = try parse(allocator, source);
    defer tree.deinit();

    try std.testing.expect(!tree.hasErrors());
    const statements = tree.rootStatements(0);
    const let_node = tree.nodes.get(statements[0]);
    const value_node = tree.nodes.get(let_node.data.lhs);

    // Top-level should be div
    try std.testing.expectEqual(.div, value_node.tag);

    // LHS of div should be a grouped_expression containing an add
    const lhs = tree.nodes.get(value_node.data.lhs);
    try std.testing.expectEqual(.grouped_expression, lhs.tag);

    const inner = tree.nodes.get(lhs.data.lhs);
    try std.testing.expectEqual(.add, inner.tag);

    // RHS of div should be number_literal '2'
    const rhs = tree.nodes.get(value_node.data.rhs);
    try std.testing.expectEqual(.number_literal, rhs.tag);
}

test "parse: precedence 1 + 2 * 3 builds mul under add" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "let x = 1 + 2 * 3";

    var tree = try parse(allocator, source);
    defer tree.deinit();

    try std.testing.expect(!tree.hasErrors());
    const statements = tree.rootStatements(0);
    const let_node = tree.nodes.get(statements[0]);
    const value_node = tree.nodes.get(let_node.data.lhs);

    // Top-level is add (lower precedence)
    try std.testing.expectEqual(.add, value_node.tag);

    // LHS is number_literal '1'
    const lhs = tree.nodes.get(value_node.data.lhs);
    try std.testing.expectEqual(.number_literal, lhs.tag);
    try std.testing.expectEqualStrings("1", tree.tokenSlice(lhs.main_token));

    // RHS is mul '2 * 3'
    const rhs = tree.nodes.get(value_node.data.rhs);
    try std.testing.expectEqual(.mul, rhs.tag);
}

test "parse: left-associative a - b - c" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "let x = a - b - c";

    var tree = try parse(allocator, source);
    defer tree.deinit();

    try std.testing.expect(!tree.hasErrors());
    const statements = tree.rootStatements(0);
    const let_node = tree.nodes.get(statements[0]);
    const value_node = tree.nodes.get(let_node.data.lhs);

    // Top-level is sub (the second -)
    try std.testing.expectEqual(.sub, value_node.tag);

    // RHS should be identifier_ref 'c'
    const rhs = tree.nodes.get(value_node.data.rhs);
    try std.testing.expectEqual(.identifier_ref, rhs.tag);
    try std.testing.expectEqualStrings("c", tree.tokenSlice(rhs.main_token));

    // LHS should be sub 'a - b' (the first -)
    const lhs = tree.nodes.get(value_node.data.lhs);
    try std.testing.expectEqual(.sub, lhs.tag);
}

test "parse: missing closing paren emits diagnostic" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "let x = (2 + 2";

    var tree = try parse(allocator, source);
    defer tree.deinit();

    try std.testing.expect(tree.hasErrors());
    try std.testing.expect(tree.diagnostics.len >= 1);
    try std.testing.expectEqual(.expected_r_paren, tree.diagnostics[0].tag);
}

test "parse: input head = 100mm" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "input head = 100mm";

    var tree = try parse(allocator, source);
    defer tree.deinit();

    try std.testing.expect(!tree.hasErrors());
    const statements = tree.rootStatements(0);
    try std.testing.expectEqual(1, statements.len);

    const input_node = tree.nodes.get(statements[0]);
    try std.testing.expectEqual(.input_statement, input_node.tag);
    try std.testing.expectEqualStrings("head", tree.tokenSlice(input_node.main_token + 1));

    const value_node = tree.nodes.get(input_node.data.lhs);
    try std.testing.expectEqual(.dimension_literal, value_node.tag);
    try std.testing.expectEqualStrings("100mm", tree.tokenSlice(value_node.main_token));
}

test "parse: mixed input and let" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "input head = 100mm let x = head";

    var tree = try parse(allocator, source);
    defer tree.deinit();

    try std.testing.expect(!tree.hasErrors());
    const statements = tree.rootStatements(0);
    try std.testing.expectEqual(2, statements.len);

    try std.testing.expectEqual(.input_statement, tree.nodes.get(statements[0]).tag);
    try std.testing.expectEqual(.let_statement, tree.nodes.get(statements[1]).tag);
}

test "parse: input rejects expression default" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "input head = 50 + 50";

    var tree = try parse(allocator, source);
    defer tree.deinit();

    // The parser accepts `input head = 50` as the input statement,
    // then `+ 50` becomes an unexpected token at the top level.
    // The input itself parses successfully with 50 as the default.
    try std.testing.expect(tree.hasErrors());
}

test "parse: input rejects identifier default" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "input head = other";

    var tree = try parse(allocator, source);
    defer tree.deinit();

    try std.testing.expect(tree.hasErrors());
    try std.testing.expectEqual(.expected_literal, tree.diagnostics[0].tag);
}

test "parse: fn_call point(100mm, 50mm)" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "let p = point(100mm, 50mm)";

    var tree = try parse(allocator, source);
    defer tree.deinit();

    try std.testing.expect(!tree.hasErrors());
    const statements = tree.rootStatements(0);
    try std.testing.expectEqual(1, statements.len);

    const let_node = tree.nodes.get(statements[0]);
    try std.testing.expectEqual(.let_statement, let_node.tag);
    try std.testing.expectEqualStrings("p", tree.tokenSlice(let_node.main_token + 1));

    const value_node = tree.nodes.get(let_node.data.lhs);
    try std.testing.expectEqual(.fn_call, value_node.tag);
    try std.testing.expectEqualStrings("point", tree.tokenSlice(value_node.main_token));

    const args = tree.callArgs(let_node.data.lhs);
    try std.testing.expectEqual(2, args.len);

    const arg0 = tree.nodes.get(args[0]);
    try std.testing.expectEqual(.dimension_literal, arg0.tag);
    try std.testing.expectEqualStrings("100mm", tree.tokenSlice(arg0.main_token));

    const arg1 = tree.nodes.get(args[1]);
    try std.testing.expectEqual(.dimension_literal, arg1.tag);
    try std.testing.expectEqualStrings("50mm", tree.tokenSlice(arg1.main_token));
}

test "parse: fn_call with expression args" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "let a = 100mm let p = point(a * 2, a / 3)";

    var tree = try parse(allocator, source);
    defer tree.deinit();

    try std.testing.expect(!tree.hasErrors());
    const statements = tree.rootStatements(0);
    try std.testing.expectEqual(2, statements.len);

    const let_p = tree.nodes.get(statements[1]);
    const call_node = tree.nodes.get(let_p.data.lhs);
    try std.testing.expectEqual(.fn_call, call_node.tag);

    const args = tree.callArgs(let_p.data.lhs);
    try std.testing.expectEqual(2, args.len);

    // First arg should be a mul expression.
    try std.testing.expectEqual(.mul, tree.nodes.get(args[0]).tag);
    // Second arg should be a div expression.
    try std.testing.expectEqual(.div, tree.nodes.get(args[1]).tag);
}

test "parse: fn_call zero args" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "let p = foo()";

    var tree = try parse(allocator, source);
    defer tree.deinit();

    try std.testing.expect(!tree.hasErrors());
    const statements = tree.rootStatements(0);
    const let_node = tree.nodes.get(statements[0]);
    const call_node = tree.nodes.get(let_node.data.lhs);
    try std.testing.expectEqual(.fn_call, call_node.tag);

    const args = tree.callArgs(let_node.data.lhs);
    try std.testing.expectEqual(0, args.len);
}

test "parse: fn_call missing closing paren" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "let p = point(100mm, 50mm";

    var tree = try parse(allocator, source);
    defer tree.deinit();

    try std.testing.expect(tree.hasErrors());
    try std.testing.expectEqual(.expected_r_paren, tree.diagnostics[0].tag);
}

test "parse: fn_def simple" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "fn foo(x: f64) { return x }";

    var tree = try parse(allocator, source);
    defer tree.deinit();

    try std.testing.expect(!tree.hasErrors());
    const statements = tree.rootStatements(0);
    try std.testing.expectEqual(1, statements.len);

    const fn_node = tree.nodes.get(statements[0]);
    try std.testing.expectEqual(.fn_def, fn_node.tag);
    try std.testing.expectEqualStrings("foo", tree.tokenSlice(fn_node.main_token + 1));

    const params = tree.fnDefParams(statements[0]);
    try std.testing.expectEqual(1, params.len);

    const param_node = tree.nodes.get(params[0]);
    try std.testing.expectEqual(.param, param_node.tag);
    try std.testing.expectEqualStrings("x", tree.tokenSlice(param_node.main_token));
    try std.testing.expectEqualStrings("f64", tree.tokenSlice(@intCast(param_node.data.lhs)));

    const body = tree.fnDefBody(statements[0]);
    try std.testing.expectEqual(0, body.len);

    const ret_node = tree.nodes.get(tree.fnDefReturn(statements[0]));
    try std.testing.expectEqual(.identifier_ref, ret_node.tag);
    try std.testing.expectEqualStrings("x", tree.tokenSlice(ret_node.main_token));
}

test "parse: fn_def with body" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 =
        \\fn double(a: length) {
        \\  let result = a * 2
        \\  return result
        \\}
    ;

    var tree = try parse(allocator, source);
    defer tree.deinit();

    try std.testing.expect(!tree.hasErrors());
    const statements = tree.rootStatements(0);
    try std.testing.expectEqual(1, statements.len);

    const params = tree.fnDefParams(statements[0]);
    try std.testing.expectEqual(1, params.len);

    const body = tree.fnDefBody(statements[0]);
    try std.testing.expectEqual(1, body.len);
    try std.testing.expectEqual(.let_statement, tree.nodes.get(body[0]).tag);

    const ret_expr = tree.fnDefReturn(statements[0]);
    try std.testing.expectEqual(.identifier_ref, tree.nodes.get(ret_expr).tag);
}

test "parse: fn_def multiple params" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "fn add(a: length, b: length) { return a + b }";

    var tree = try parse(allocator, source);
    defer tree.deinit();

    try std.testing.expect(!tree.hasErrors());
    const statements = tree.rootStatements(0);

    const params = tree.fnDefParams(statements[0]);
    try std.testing.expectEqual(2, params.len);

    const p0 = tree.nodes.get(params[0]);
    try std.testing.expectEqualStrings("a", tree.tokenSlice(p0.main_token));
    try std.testing.expectEqualStrings("length", tree.tokenSlice(@intCast(p0.data.lhs)));

    const p1 = tree.nodes.get(params[1]);
    try std.testing.expectEqualStrings("b", tree.tokenSlice(p1.main_token));
    try std.testing.expectEqualStrings("length", tree.tokenSlice(@intCast(p1.data.lhs)));

    const ret_expr = tree.fnDefReturn(statements[0]);
    try std.testing.expectEqual(.add, tree.nodes.get(ret_expr).tag);
}

test "parse: fn_def no params" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "fn zero() { return 42 }";

    var tree = try parse(allocator, source);
    defer tree.deinit();

    try std.testing.expect(!tree.hasErrors());
    const statements = tree.rootStatements(0);

    const params = tree.fnDefParams(statements[0]);
    try std.testing.expectEqual(0, params.len);

    const ret_expr = tree.fnDefReturn(statements[0]);
    try std.testing.expectEqual(.number_literal, tree.nodes.get(ret_expr).tag);
}

test "parse: fn_def missing return" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "fn foo(x: f64) { let y = x }";

    var tree = try parse(allocator, source);
    defer tree.deinit();

    try std.testing.expect(tree.hasErrors());
    // Should hit expected_return after the let binding when it sees '}'
    var found_return_error = false;
    for (tree.diagnostics) |diag| {
        if (diag.tag == .expected_return) found_return_error = true;
    }
    try std.testing.expect(found_return_error);
}

test "parse: fn_def and let coexist" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 =
        \\fn double(x: f64) { return x * 2 }
        \\let y = double(5)
    ;

    var tree = try parse(allocator, source);
    defer tree.deinit();

    try std.testing.expect(!tree.hasErrors());
    const statements = tree.rootStatements(0);
    try std.testing.expectEqual(2, statements.len);
    try std.testing.expectEqual(.fn_def, tree.nodes.get(statements[0]).tag);
    try std.testing.expectEqual(.let_statement, tree.nodes.get(statements[1]).tag);
}
