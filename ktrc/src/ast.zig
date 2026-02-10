const std = @import("std");
const lexer = @import("lexer.zig");

pub const TokenIndex = u32;
pub const NodeIndex = u32;

pub const Diagnostic = struct {
    tag: Tag,
    token: TokenIndex,

    pub const Tag = enum {
        // ------------------------------
        // Parser
        // ------------------------------

        expected_identifier,
        expected_equal,
        expected_expression,
        expected_literal,
        expected_r_paren,
        unexpected_token,

        expected_l_brace,
        expected_r_brace,
        expected_colon,
        expected_type_name,
        expected_return,

        // ------------------------------
        // Semantic Analysis
        // ------------------------------

        duplicate_binding,
        undefined_reference,
        type_mismatch,
        unknown_function,
        wrong_argument_count,
        argument_type_mismatch,
        duplicate_function,

        pub fn message(self: Tag) []const u8 {
            return switch (self) {
                .expected_identifier => "expected identifier",
                .expected_equal => "expected '='",
                .expected_expression => "expected expression",
                .expected_literal => "expected literal value (e.g. 100mm, 50%, 42)",
                .expected_r_paren => "expected ')'",
                .unexpected_token => "unexpected token",
                .expected_l_brace => "expected '{'",
                .expected_r_brace => "expected '}'",
                .expected_colon => "expected ':'",
                .expected_type_name => "expected type name",
                .expected_return => "expected 'return'",
                .duplicate_binding => "duplicate binding",
                .undefined_reference => "undefined reference",
                .type_mismatch => "type mismatch in arithmetic expression",
                .unknown_function => "unknown function",
                .wrong_argument_count => "wrong number of arguments",
                .argument_type_mismatch => "argument type mismatch",
                .duplicate_function => "duplicate function name",
            };
        }
    };
};

pub const TokenList = std.MultiArrayList(lexer.Token);
pub const NodeList = std.MultiArrayList(Node);

pub const Node = struct {
    tag: Tag,
    main_token: TokenIndex,
    data: Data,

    pub const Tag = enum(u8) {
        // ------------------------------
        // Root
        // ------------------------------

        /// Program root.
        /// main_token: unused (0). lhs: start index into extra_data.
        /// rhs: end index into extra_data (exclusive).
        /// extra_data[lhs..rhs] contains NodeIndex values of top-level statements.
        root,

        // ------------------------------
        // Statements
        // ------------------------------

        /// `let <name> = <expr>`.
        /// main_token: `let` token (name = main_token + 1).
        /// lhs: value expression node index. rhs: unused (0).
        let_statement,

        /// `input <name> = <expr>`.
        /// main_token: `input` token (name = main_token + 1).
        /// lhs: default value expression node index. rhs: unused (0).
        input_statement,

        /// `fn <name>(<params>) { <body> return <expr> }`.
        /// main_token: `fn` token (name = main_token + 1).
        /// lhs: start index into extra_data. rhs: end index (exclusive).
        /// extra_data[lhs..rhs] layout:
        ///   [param_count, param_node_0, ..., param_node_N-1,
        ///    body_stmt_0, ..., body_stmt_M-1, return_expr_node]
        fn_def,

        /// Typed parameter: `name : type`.
        /// main_token: identifier (param name).
        /// lhs: token index of type_name. rhs: unused (0).
        param,

        /// `return <expr>`.
        /// main_token: `return` token.
        /// lhs: expression node index. rhs: unused (0).
        return_stmt,

        // ------------------------------
        // Expressions
        // ------------------------------

        /// A reference to a previously defined binding, e.g. `x`.
        /// main_token: identifier token. data: unused.
        identifier_ref,

        // ------------------------------
        // Binary Arithmetic
        // ------------------------------

        /// `lhs + rhs`. main_token: `+` token. lhs: left node. rhs: right node.
        add,
        /// `lhs - rhs`. main_token: `-` token. lhs: left node. rhs: right node.
        sub,
        /// `lhs * rhs`. main_token: `*` token. lhs: left node. rhs: right node.
        mul,
        /// `lhs / rhs`. main_token: `/` token. lhs: left node. rhs: right node.
        div,

        // ------------------------------
        // Calls
        // ------------------------------

        /// `name(arg, ...)`. main_token: identifier (function name).
        /// lhs: start index into extra_data. rhs: end index (exclusive).
        /// extra_data[lhs..rhs] contains NodeIndex values for each argument.
        fn_call,

        // ------------------------------
        // Grouping
        // ------------------------------

        /// `( expr )`. main_token: `(` token. lhs: inner expression node. rhs: unused (0).
        grouped_expression,

        // ------------------------------
        // Literals
        // ------------------------------

        /// A number with a length unit, e.g. `100mm`.
        /// main_token: dimension_literal token. data: unused.
        dimension_literal,
        /// A number with `%`, e.g. `50%`.
        /// main_token: percentage_literal token. data: unused.
        percentage_literal,
        /// A bare number, e.g. `100`.
        /// main_token: number_literal token. data: unused.
        number_literal,
    };

    pub const Data = struct {
        lhs: u32,
        rhs: u32,
    };
};

pub const Ast = struct {
    /// Borrowed reference to the original source. Caller must keep it alive
    /// for the lifetime of the Ast and any Sema derived from it.
    source: [:0]const u8,
    tokens: TokenList,
    nodes: NodeList,
    extra_data: []const u32,
    diagnostics: []const Diagnostic,
    allocator: std.mem.Allocator,

    /// Returns true if any diagnostics were emitted during parsing.
    pub fn hasErrors(self: Ast) bool {
        return self.diagnostics.len > 0;
    }

    /// Returns the slice of source corresponding to the token at `token_index`.
    pub fn tokenSlice(self: Ast, token_index: TokenIndex) []const u8 {
        const start = self.tokens.items(.start)[token_index];
        const end = self.tokens.items(.end)[token_index];
        return self.source[start..end];
    }

    /// Returns the list of statement node indices for a `root` node.
    pub fn rootStatements(self: Ast, root_index: NodeIndex) []const NodeIndex {
        const data = self.nodes.items(.data)[root_index];
        return self.extra_data[data.lhs..data.rhs];
    }

    /// Returns the list of argument node indices for a `fn_call` node.
    pub fn callArgs(self: Ast, call_index: NodeIndex) []const NodeIndex {
        const data = self.nodes.items(.data)[call_index];
        return self.extra_data[data.lhs..data.rhs];
    }

    /// Returns the param node indices for a `fn_def` node.
    pub fn fnDefParams(self: Ast, fn_def_index: NodeIndex) []const NodeIndex {
        const data = self.nodes.items(.data)[fn_def_index];
        const extra = self.extra_data[data.lhs..data.rhs];
        const param_count = extra[0];
        return extra[1 .. 1 + param_count];
    }

    /// Returns the body let-statement node indices for a `fn_def` node.
    pub fn fnDefBody(self: Ast, fn_def_index: NodeIndex) []const NodeIndex {
        const data = self.nodes.items(.data)[fn_def_index];
        const extra = self.extra_data[data.lhs..data.rhs];
        const param_count = extra[0];
        // Layout: [param_count, params..., body_stmts..., return_expr]
        // body_stmts = extra[1 + param_count .. extra.len - 1]
        return extra[1 + param_count .. extra.len - 1];
    }

    /// Returns the return expression node index for a `fn_def` node.
    pub fn fnDefReturn(self: Ast, fn_def_index: NodeIndex) NodeIndex {
        const data = self.nodes.items(.data)[fn_def_index];
        const extra = self.extra_data[data.lhs..data.rhs];
        return extra[extra.len - 1];
    }

    pub fn deinit(self: *Ast) void {
        self.tokens.deinit(self.allocator);
        self.nodes.deinit(self.allocator);
        self.allocator.free(self.extra_data);
        self.allocator.free(self.diagnostics);
        self.* = undefined;
    }
};

/// Compute 1-based line and column numbers for a byte offset in source text.
pub fn computeLineCol(source: []const u8, byte_offset: usize) struct { usize, usize } {
    var line: usize = 1;
    var col: usize = 1;
    for (source[0..@min(byte_offset, source.len)]) |c| {
        if (c == '\n') {
            line += 1;
            col = 1;
        } else {
            col += 1;
        }
    }
    return .{ line, col };
}

// --- Tests ---

test "node layout" {
    try std.testing.expectEqual(1, @sizeOf(Node.Tag));
    try std.testing.expectEqual(8, @sizeOf(Node.Data));
}

test "structure for let x = 100mm" {
    const allocator = std.testing.allocator;
    const source: [:0]const u8 = "let x = 100mm";

    var tokens = TokenList{};
    try tokens.append(allocator, .{ .tag = .let, .start = 0, .end = 3 });
    try tokens.append(allocator, .{ .tag = .identifier, .start = 4, .end = 5 });
    try tokens.append(allocator, .{ .tag = .equal, .start = 6, .end = 7 });
    try tokens.append(allocator, .{ .tag = .dimension_literal, .start = 8, .end = 13 });
    try tokens.append(allocator, .{ .tag = .eof, .start = 13, .end = 13 });

    var nodes = NodeList{};
    try nodes.append(allocator, .{
        .tag = .root,
        .main_token = 0,
        .data = .{ .lhs = 0, .rhs = 1 },
    });
    try nodes.append(allocator, .{
        .tag = .let_statement,
        .main_token = 0,
        .data = .{ .lhs = 2, .rhs = 0 },
    });
    try nodes.append(allocator, .{
        .tag = .dimension_literal,
        .main_token = 3,
        .data = .{ .lhs = 0, .rhs = 0 },
    });

    const extra = try allocator.dupe(u32, &.{1});
    const diagnostics = try allocator.dupe(Diagnostic, &.{});

    var tree = Ast{
        .allocator = allocator,
        .source = source,
        .tokens = tokens,
        .nodes = nodes,
        .extra_data = extra,
        .diagnostics = diagnostics,
    };
    defer tree.deinit();

    try std.testing.expect(!tree.hasErrors());

    const root_index: NodeIndex = 0;
    try std.testing.expectEqual(.root, tree.nodes.get(root_index).tag);
    const statements = tree.rootStatements(root_index);
    try std.testing.expectEqual(1, statements.len);

    const let_node = tree.nodes.get(statements[0]);
    try std.testing.expectEqual(.let_statement, let_node.tag);
    try std.testing.expectEqualStrings(tree.tokenSlice(let_node.main_token + 1), "x");

    const value_node = tree.nodes.get(let_node.data.lhs);
    try std.testing.expectEqual(.dimension_literal, value_node.tag);
    try std.testing.expectEqualStrings(tree.tokenSlice(value_node.main_token), "100mm");
}
