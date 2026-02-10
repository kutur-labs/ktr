const std = @import("std");
const LengthUnit = @import("unit.zig").LengthUnit;

pub const Token = struct {
    tag: Tag,
    start: u32,
    end: u32, // exclusive

    pub const Tag = enum(u8) {
        // ------------------------------
        // Keywords
        // ------------------------------

        /// `let`
        let,
        /// `input`
        input,
        /// `fn`
        @"fn",
        /// `return`
        @"return",

        // ------------------------------
        // Identifiers
        // ------------------------------

        /// An identifier, e.g. `head`, `neck_quarter`.
        identifier,

        // ------------------------------
        // Literals
        // ------------------------------

        /// A bare number, e.g. `100`.
        number_literal,
        /// A number with a length unit, e.g. `100mm`, `25cm`.
        dimension_literal,
        /// A number followed by `%`, e.g. `50%`.
        percentage_literal,

        // ------------------------------
        // Operators
        // ------------------------------

        /// `=` (assignment)
        equal,
        /// `+`
        plus,
        /// `-`
        minus,
        /// `*`
        star,
        /// `/`
        slash,
        /// `(`
        l_paren,
        /// `)`
        r_paren,
        /// `,`
        comma,
        /// `.`
        dot,
        /// `{`
        l_brace,
        /// `}`
        r_brace,
        /// `:`
        colon,

        // ------------------------------
        // Special
        // ------------------------------

        /// An unrecognized character.
        invalid,
        /// The end of the input buffer.
        eof,
    };
};

pub const Lexer = struct {
    input: [:0]const u8,
    i: u32,

    pub fn init(input: [:0]const u8) Lexer {
        return .{ .input = input, .i = 0 };
    }

    pub fn lexeme(self: *const Lexer, tok: Token) []const u8 {
        return self.input[tok.start..tok.end];
    }

    fn peek(self: *const Lexer) u8 {
        return self.input[self.i]; // sentinel returns 0 at EOF
    }

    fn advance(self: *Lexer) void {
        if (self.i < self.input.len) self.i += 1;
    }

    fn skipWhitespace(self: *Lexer) void {
        while (std.ascii.isWhitespace(self.peek())) {
            self.advance();
        }
    }

    fn isIdentContinue(c: u8) bool {
        return std.ascii.isAlphanumeric(c) or c == '_';
    }

    const keywords = std.StaticStringMap(Token.Tag).initComptime(.{
        .{ "let", .let },
        .{ "input", .input },
        .{ "fn", .@"fn" },
        .{ "return", .@"return" },
    });

    fn readIdentifier(self: *Lexer) Token {
        const start = self.i;
        while (isIdentContinue(self.peek())) {
            self.advance();
        }
        const text = self.input[start..self.i];
        const tag: Token.Tag = keywords.get(text) orelse .identifier;
        return .{ .tag = tag, .start = start, .end = self.i };
    }

    fn readNumber(self: *Lexer) Token {
        const start = self.i;
        while (std.ascii.isDigit(self.peek())) {
            self.advance();
        }

        // Decimal part: '.' followed by at least one digit.
        if (self.peek() == '.' and self.i + 1 < self.input.len and std.ascii.isDigit(self.input[self.i + 1])) {
            self.advance(); // consume '.'
            while (std.ascii.isDigit(self.peek())) self.advance();
        }

        if (self.peek() == '%') {
            self.advance();
            return .{ .tag = .percentage_literal, .start = start, .end = self.i };
        }

        // Try unit suffix: consume full alpha run, then validate.
        const suffix_start = self.i;
        while (std.ascii.isAlphabetic(self.peek())) {
            self.advance();
        }
        const suffix = self.input[suffix_start..self.i];

        if (suffix.len > 0 and LengthUnit.fromStr(suffix) != null) {
            return .{ .tag = .dimension_literal, .start = start, .end = self.i };
        }

        // Not a known unit -- rewind; let the alpha run lex as a separate token.
        self.i = suffix_start;
        return .{ .tag = .number_literal, .start = start, .end = self.i };
    }

    pub fn next(self: *Lexer) Token {
        self.skipWhitespace();
        if (self.peek() == 0) return .{ .tag = .eof, .start = self.i, .end = self.i };

        const c = self.peek();

        const single_char_tag: ?Token.Tag = switch (c) {
            '=' => .equal,
            '+' => .plus,
            '-' => .minus,
            '*' => .star,
            '/' => .slash,
            '(' => .l_paren,
            ')' => .r_paren,
            ',' => .comma,
            '.' => .dot,
            '{' => .l_brace,
            '}' => .r_brace,
            ':' => .colon,
            else => null,
        };
        if (single_char_tag) |tag| {
            const start = self.i;
            self.advance();
            return .{ .tag = tag, .start = start, .end = self.i };
        }

        if (std.ascii.isAlphabetic(c) or c == '_') return self.readIdentifier();
        if (std.ascii.isDigit(c)) return self.readNumber();

        const start = self.i;
        self.advance();
        return .{ .tag = .invalid, .start = start, .end = self.i };
    }
};

// --- Tests ---

test "lexer: dimension literal" {
    var lex = Lexer.init("let x = 100mm");

    try std.testing.expectEqual(lex.next().tag, .let);
    try std.testing.expectEqual(lex.next().tag, .identifier);
    try std.testing.expectEqual(lex.next().tag, .equal);

    const dim = lex.next();
    try std.testing.expectEqual(dim.tag, .dimension_literal);
    try std.testing.expectEqual(dim.start, 8);
    try std.testing.expectEqual(dim.end, 13);
    try std.testing.expectEqualStrings(lex.lexeme(dim), "100mm");
}

test "lexer: percentage literal" {
    var lex = Lexer.init("let y = 50%");

    try std.testing.expectEqual(lex.next().tag, .let);
    try std.testing.expectEqual(lex.next().tag, .identifier);
    try std.testing.expectEqual(lex.next().tag, .equal);

    const pct = lex.next();
    try std.testing.expectEqual(pct.tag, .percentage_literal);
    try std.testing.expectEqualStrings(lex.lexeme(pct), "50%");
}

test "lexer: unitless number" {
    var lex = Lexer.init("let x = 100");

    try std.testing.expectEqual(lex.next().tag, .let);
    try std.testing.expectEqual(lex.next().tag, .identifier);
    try std.testing.expectEqual(lex.next().tag, .equal);

    const num = lex.next();
    try std.testing.expectEqual(num.tag, .number_literal);
    try std.testing.expectEqual(num.start, 8);
    try std.testing.expectEqual(num.end, 11);

    try std.testing.expectEqual(lex.next().tag, .eof);
}

test "lexer: mm and cm as identifiers outside number context" {
    var lex = Lexer.init("let mm = 5");

    try std.testing.expectEqual(lex.next().tag, .let);

    const ident = lex.next();
    try std.testing.expectEqual(ident.tag, .identifier);
    try std.testing.expectEqualStrings(lex.lexeme(ident), "mm");
}

test "lexer: underscore identifiers" {
    var lex = Lexer.init("let neck_quarter = 100mm");

    try std.testing.expectEqual(lex.next().tag, .let);

    const ident = lex.next();
    try std.testing.expectEqual(ident.tag, .identifier);
    try std.testing.expectEqualStrings(lex.lexeme(ident), "neck_quarter");
}

test "lexer: unknown suffix after number rewinds to number_literal" {
    var lex = Lexer.init("100mma");

    // "mma" is not a known unit, so 100 is a bare number and "mma" is an identifier.
    const num = lex.next();
    try std.testing.expectEqual(num.tag, .number_literal);
    try std.testing.expectEqualStrings(lex.lexeme(num), "100");

    const ident = lex.next();
    try std.testing.expectEqual(ident.tag, .identifier);
    try std.testing.expectEqualStrings(lex.lexeme(ident), "mma");

    try std.testing.expectEqual(lex.next().tag, .eof);
}

test "lexer: invalid character produces invalid token" {
    var lex = Lexer.init("let x @ 100");

    try std.testing.expectEqual(lex.next().tag, .let);
    try std.testing.expectEqual(lex.next().tag, .identifier);

    const inv = lex.next();
    try std.testing.expectEqual(inv.tag, .invalid);
    try std.testing.expectEqualStrings(lex.lexeme(inv), "@");

    try std.testing.expectEqual(lex.next().tag, .number_literal);
    try std.testing.expectEqual(lex.next().tag, .eof);
}

test "lexer: decimal number" {
    var lex = Lexer.init("3.14");

    const num = lex.next();
    try std.testing.expectEqual(num.tag, .number_literal);
    try std.testing.expectEqualStrings(lex.lexeme(num), "3.14");

    try std.testing.expectEqual(lex.next().tag, .eof);
}

test "lexer: decimal dimension literal" {
    var lex = Lexer.init("0.5mm");

    const dim = lex.next();
    try std.testing.expectEqual(dim.tag, .dimension_literal);
    try std.testing.expectEqualStrings(lex.lexeme(dim), "0.5mm");

    try std.testing.expectEqual(lex.next().tag, .eof);
}

test "lexer: decimal percentage literal" {
    var lex = Lexer.init("0.5%");

    const pct = lex.next();
    try std.testing.expectEqual(pct.tag, .percentage_literal);
    try std.testing.expectEqualStrings(lex.lexeme(pct), "0.5%");

    try std.testing.expectEqual(lex.next().tag, .eof);
}

test "lexer: arithmetic operators" {
    var lex = Lexer.init("a + b * 2");

    try std.testing.expectEqual(lex.next().tag, .identifier);
    try std.testing.expectEqual(lex.next().tag, .plus);
    try std.testing.expectEqual(lex.next().tag, .identifier);
    try std.testing.expectEqual(lex.next().tag, .star);
    try std.testing.expectEqual(lex.next().tag, .number_literal);
    try std.testing.expectEqual(lex.next().tag, .eof);
}

test "lexer: parentheses" {
    var lex = Lexer.init("(1 + 2)");

    try std.testing.expectEqual(lex.next().tag, .l_paren);
    try std.testing.expectEqual(lex.next().tag, .number_literal);
    try std.testing.expectEqual(lex.next().tag, .plus);
    try std.testing.expectEqual(lex.next().tag, .number_literal);
    try std.testing.expectEqual(lex.next().tag, .r_paren);
    try std.testing.expectEqual(lex.next().tag, .eof);
}

test "lexer: all arithmetic operators" {
    var lex = Lexer.init("a + b - c * d / e");

    try std.testing.expectEqual(lex.next().tag, .identifier);
    try std.testing.expectEqual(lex.next().tag, .plus);
    try std.testing.expectEqual(lex.next().tag, .identifier);
    try std.testing.expectEqual(lex.next().tag, .minus);
    try std.testing.expectEqual(lex.next().tag, .identifier);
    try std.testing.expectEqual(lex.next().tag, .star);
    try std.testing.expectEqual(lex.next().tag, .identifier);
    try std.testing.expectEqual(lex.next().tag, .slash);
    try std.testing.expectEqual(lex.next().tag, .identifier);
    try std.testing.expectEqual(lex.next().tag, .eof);
}

test "lexer: input keyword" {
    var lex = Lexer.init("input head = 100mm");

    try std.testing.expectEqual(lex.next().tag, .input);
    try std.testing.expectEqual(lex.next().tag, .identifier);
    try std.testing.expectEqual(lex.next().tag, .equal);
    try std.testing.expectEqual(lex.next().tag, .dimension_literal);
    try std.testing.expectEqual(lex.next().tag, .eof);
}

test "lexer: input as identifier outside keyword context" {
    var lex = Lexer.init("let input_size = 5");

    try std.testing.expectEqual(lex.next().tag, .let);

    const ident = lex.next();
    try std.testing.expectEqual(ident.tag, .identifier);
    try std.testing.expectEqualStrings(lex.lexeme(ident), "input_size");
}

test "lexer: comma token" {
    var lex = Lexer.init("a, b");

    try std.testing.expectEqual(lex.next().tag, .identifier);
    try std.testing.expectEqual(lex.next().tag, .comma);
    try std.testing.expectEqual(lex.next().tag, .identifier);
    try std.testing.expectEqual(lex.next().tag, .eof);
}

test "lexer: dot token" {
    var lex = Lexer.init("a.b");

    try std.testing.expectEqual(lex.next().tag, .identifier);
    try std.testing.expectEqual(lex.next().tag, .dot);
    try std.testing.expectEqual(lex.next().tag, .identifier);
    try std.testing.expectEqual(lex.next().tag, .eof);
}

test "lexer: function call syntax" {
    var lex = Lexer.init("point(100mm, 50mm)");

    try std.testing.expectEqual(lex.next().tag, .identifier);
    try std.testing.expectEqual(lex.next().tag, .l_paren);
    try std.testing.expectEqual(lex.next().tag, .dimension_literal);
    try std.testing.expectEqual(lex.next().tag, .comma);
    try std.testing.expectEqual(lex.next().tag, .dimension_literal);
    try std.testing.expectEqual(lex.next().tag, .r_paren);
    try std.testing.expectEqual(lex.next().tag, .eof);
}

test "lexer: dot does not interfere with decimal numbers" {
    var lex = Lexer.init("3.14");

    const num = lex.next();
    try std.testing.expectEqual(num.tag, .number_literal);
    try std.testing.expectEqualStrings(lex.lexeme(num), "3.14");
    try std.testing.expectEqual(lex.next().tag, .eof);
}

test "lexer: fn keyword" {
    var lex = Lexer.init("fn foo");

    try std.testing.expectEqual(lex.next().tag, .@"fn");
    try std.testing.expectEqual(lex.next().tag, .identifier);
    try std.testing.expectEqual(lex.next().tag, .eof);
}

test "lexer: return keyword" {
    var lex = Lexer.init("return x");

    try std.testing.expectEqual(lex.next().tag, .@"return");
    try std.testing.expectEqual(lex.next().tag, .identifier);
    try std.testing.expectEqual(lex.next().tag, .eof);
}

test "lexer: braces" {
    var lex = Lexer.init("{ }");

    try std.testing.expectEqual(lex.next().tag, .l_brace);
    try std.testing.expectEqual(lex.next().tag, .r_brace);
    try std.testing.expectEqual(lex.next().tag, .eof);
}

test "lexer: colon" {
    var lex = Lexer.init("x : f64");

    try std.testing.expectEqual(lex.next().tag, .identifier);
    try std.testing.expectEqual(lex.next().tag, .colon);
    try std.testing.expectEqual(lex.next().tag, .identifier);
    try std.testing.expectEqual(lex.next().tag, .eof);
}

test "lexer: fn definition syntax" {
    var lex = Lexer.init("fn foo(x: f64) { return x }");

    try std.testing.expectEqual(lex.next().tag, .@"fn");
    try std.testing.expectEqual(lex.next().tag, .identifier);
    try std.testing.expectEqual(lex.next().tag, .l_paren);
    try std.testing.expectEqual(lex.next().tag, .identifier);
    try std.testing.expectEqual(lex.next().tag, .colon);
    try std.testing.expectEqual(lex.next().tag, .identifier);
    try std.testing.expectEqual(lex.next().tag, .r_paren);
    try std.testing.expectEqual(lex.next().tag, .l_brace);
    try std.testing.expectEqual(lex.next().tag, .@"return");
    try std.testing.expectEqual(lex.next().tag, .identifier);
    try std.testing.expectEqual(lex.next().tag, .r_brace);
    try std.testing.expectEqual(lex.next().tag, .eof);
}

test "lexer: fn as identifier prefix" {
    var lex = Lexer.init("let fn_name = 5");

    try std.testing.expectEqual(lex.next().tag, .let);

    const ident = lex.next();
    try std.testing.expectEqual(ident.tag, .identifier);
    try std.testing.expectEqualStrings(lex.lexeme(ident), "fn_name");
}
