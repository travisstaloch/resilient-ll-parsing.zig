//! adapted from https://matklad.github.io/2023/05/21/resilient-ll-parsing-tutorial.html
//! and https://github.com/matklad/resilient-ll-parsing/
//!
//! $ zig build run -- examples/1.pl
//!

const std = @import("std");
const common = @import("common.zig");
const mem = std.mem;
const assert = std.debug.assert;
const ComptimeStringMap = @import("ct_str_map.zig").ComptimeStringMap;

pub fn main() !void {
    // var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    // const alloc = arena.allocator();
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa.deinit();
    const alloc = gpa.allocator();
    const args = try std.process.argsAlloc(alloc);
    defer std.process.argsFree(alloc, args);
    if (args.len < 2) return error.MissingfilepathArg;
    const filepath = args[1];
    const f = try std.fs.cwd().openFile(filepath, .{});
    defer f.close();
    const input = try f.readToEndAlloc(alloc, std.math.maxInt(u32));
    defer alloc.free(input);
    var tree = try parse(alloc, input, filepath);
    defer tree.deinit(alloc);
    std.debug.print("{any}\n", .{tree});
}

pub const Token = struct {
    kind: Kind,
    src: []const u8,

    pub const Kind = enum(u8) {
        err,
        eof,

        lparen,
        rparen,
        lcurly,
        rcurly,
        eq,
        semi,
        comma,
        colon,
        arrow,
        plus,
        minus,
        star,
        slash,

        kwd_fn,
        kwd_let,
        kwd_return,
        kwd_true,
        kwd_false,

        name,
        int,
    };

    pub fn init(kind: Token.Kind, src: []const u8) Token {
        return .{ .kind = kind, .src = src };
    }

    pub fn format(
        t: Token,
        comptime fmt: []const u8,
        options: std.fmt.FormatOptions,
        writer: anytype,
    ) !void {
        _ = fmt;
        _ = options;
        try writer.print("{s} '{s}'", .{ @tagName(t.kind), t.src });
        // try writer.print("'{s}'", .{t.src});
    }
};

pub const Tree = struct {
    kind: Tree.Kind,
    children: std.ArrayListUnmanaged(Child) = .{},

    pub const Kind = enum {
        err,
        file,
        function,
        expr_type,
        param_list,
        param,
        block,
        stmt_let,
        stmt_ret,
        stmt_expr,
        expr_lit,
        expr_name,
        expr_paren,
        expr_binary,
        expr_call,
        arg_list,
        arg,
    };

    pub fn deinit(t: *Tree, alloc: mem.Allocator) void {
        for (t.children.items) |*child| child.deinit(alloc);
        t.children.deinit(alloc);
    }

    pub fn format(
        t: Tree,
        comptime fmt: []const u8,
        options: std.fmt.FormatOptions,
        writer: anytype,
    ) !void {
        _ = fmt;
        _ = options;
        try t.print(writer, 0);
    }

    fn print(t: Tree, writer: anytype, level: usize) !void {
        try writer.writeByteNTimes(' ', level * 2);
        _ = try writer.write(@tagName(t.kind));
        try writer.writeByte('\n');
        for (t.children.items) |child| {
            switch (child) {
                .token => |token| {
                    try writer.writeByteNTimes(' ', level * 2);
                    try writer.print("  '{s}'\n", .{token.src});
                    // try writer.print("  {}\n", .{token});
                },
                .tree => |tree| try tree.print(writer, level + 1),
            }
        }
    }
};

const Child = union(enum) {
    token: Token,
    tree: Tree,

    pub fn deinit(c: *Child, alloc: mem.Allocator) void {
        if (c.* == .tree) c.tree.deinit(alloc);
    }
};

pub fn parse(alloc: mem.Allocator, src: []const u8, filepath: []const u8) !Tree {
    const lexed = try lex(alloc, src);
    // for (lexed.spans, 0..) |span, i|
    //     std.debug.print("{s}:'{s}', ", .{ @tagName(lexed.kinds[i]), src[span[0]..span[1]] });
    var p = Parser.init(lexed, src, filepath, alloc);
    defer p.deinit();
    p.file();
    return p.build_tree();
}

const token_map = ComptimeStringMap(Token.Kind, .{
    .{ "(", .lparen },
    .{ ")", .rparen },
    .{ "{", .lcurly },
    .{ "}", .rcurly },
    .{ "=", .eq },
    .{ ";", .semi },
    .{ ",", .comma },
    .{ ":", .colon },
    .{ "->", .arrow },
    .{ "+", .plus },
    .{ "-", .minus },
    .{ "*", .star },
    .{ "/", .slash },
    .{ "fn", .kwd_fn },
    .{ "let", .kwd_let },
    .{ "return", .kwd_return },
    .{ "true", .kwd_true },
    .{ "false", .kwd_false },
});

const Lexed = struct {
    kinds: []const Token.Kind,
    spans: []const [2]u32,

    pub fn deinit(l: *Lexed, alloc: mem.Allocator) void {
        alloc.free(l.kinds);
        alloc.free(l.spans);
    }
};

fn lex(alloc: mem.Allocator, src: []const u8) !Lexed {
    var kinds = std.ArrayList(Token.Kind).init(alloc);
    var spans = std.ArrayList([2]u32).init(alloc);

    var pos: u32 = 0;
    while (true) {
        pos += common.predLength(std.ascii.isWhitespace, src[pos..]) orelse 0;
        // std.debug.print("pos={} src.len={}\n", .{ pos, src.len });
        if (pos >= src.len) break;

        const start = pos;
        const kind: Token.Kind = kind: {
            if (token_map.getPartial(src[pos..])) |token| {
                pos += @intCast(token.key.len);
                break :kind token.value;
            }
            if (common.predLength(std.ascii.isDigit, src[pos..])) |len| {
                pos += len;
                break :kind .int;
            }
            if (std.ascii.isAlphabetic(src[pos])) {
                pos += 1;
                pos += common.predLength(common.name_char, src[pos..]) orelse 0;
                break :kind .name;
            }
            break :kind .err;
        };
        // std.debug.print("kind={} pos={} start={}\n", .{ kind, pos, start });
        assert(pos > start);
        // const token_src = src[start..pos];
        // const token = Token{ .kind = kind, .src = token_src };
        // std.debug.print("{}\n", .{token});
        try kinds.append(kind);
        try spans.append(.{ start, pos });
    }

    return .{
        .kinds = try kinds.toOwnedSlice(),
        .spans = try spans.toOwnedSlice(),
    };
}

const Event = union(enum) {
    open: Tree.Kind,
    close,
    advance,
};

pub const MarkOpened = enum(usize) {
    _,
    pub fn to_closed(m: MarkOpened) MarkClosed {
        return @enumFromInt(m.to_int());
    }
    pub fn to_int(m: MarkOpened) usize {
        return @intFromEnum(m);
    }
};

pub const MarkClosed = enum(usize) {
    _,
    pub fn to_opened(m: MarkClosed) MarkOpened {
        return @enumFromInt(m.to_int());
    }
    pub fn to_int(m: MarkClosed) usize {
        return @intFromEnum(m);
    }
};

pub const Parser = struct {
    lexed: Lexed,
    src: []const u8,
    filepath: []const u8,
    pos: usize,
    fuel: u32,
    events: std.ArrayListUnmanaged(Event) = .{},
    alloc: mem.Allocator,

    pub fn init(
        lexed: Lexed,
        src: []const u8,
        filepath: []const u8,
        alloc: mem.Allocator,
    ) Parser {
        return .{
            .lexed = lexed,
            .src = src,
            .pos = 0,
            .fuel = 256,
            .alloc = alloc,
            .filepath = filepath,
        };
    }

    pub fn deinit(p: *Parser) void {
        p.lexed.deinit(p.alloc);
        p.events.deinit(p.alloc);
    }

    fn build_tree(self: *Parser) !Tree {
        assert(self.events.pop() == .close);
        var pos: usize = 0;
        var stack = std.ArrayList(Tree).init(self.alloc);
        defer stack.deinit();
        for (self.events.items) |event| {
            // std.debug.print("build_tree() event={}\n", .{event});
            switch (event) {
                .open => |kind| try stack.append(.{ .kind = kind }),
                .close => {
                    const tree = stack.pop();
                    try stack.items[stack.items.len - 1].children.append(
                        self.alloc,
                        .{ .tree = tree },
                    );
                },
                .advance => {
                    try stack.items[stack.items.len - 1].children.append(
                        self.alloc,
                        .{ .token = self.tokenAt(pos) },
                    );
                    pos += 1;
                },
            }
        }

        const tree = stack.pop();
        assert(stack.items.len == 0);
        assert(pos == self.lexed.kinds.len);
        return tree;
    }

    /// File = Fn*
    fn file(p: *Parser) void {
        const m = p.open();
        while (!p.eof()) {
            if (p.at(.kwd_fn)) {
                p.func();
            } else p.advance_with_error("expected a function");
        }
        _ = p.close(m, .file);
    }

    /// Fn = 'fn' 'name' ParamList ('->' TypeExpr)? Block
    fn func(p: *Parser) void {
        // std.debug.print("func()\n", .{});
        assert(p.at(.kwd_fn));
        const m = p.open();
        p.expect(.kwd_fn);
        p.expect(.name);
        if (p.at(.lparen)) {
            p.param_list();
        }
        if (p.eat(.arrow)) {
            p.type_expr();
        }
        if (p.at(.lcurly)) {
            p.block();
        }
        _ = p.close(m, .function);
    }

    const PARAM_LIST_RECOVERY = [_]Token.Kind{ .kwd_fn, .lcurly };
    /// ParamList = '(' Param* ')'
    fn param_list(p: *Parser) void {
        // std.debug.print("param_list()\n", .{});
        assert(p.at(.lparen));
        const m = p.open();

        p.expect(.lparen);
        while (!p.at(.rparen) and !p.eof()) {
            if (p.at(.name)) {
                p.param();
            } else {
                if (p.at_any(&PARAM_LIST_RECOVERY)) {
                    break;
                }
                p.advance_with_error("expected parameter");
            }
        }
        p.expect(.rparen);

        _ = p.close(m, .param_list);
    }

    /// Param = 'name' ':' TypeExpr ','?
    fn param(p: *Parser) void {
        assert(p.at(.name));
        const m = p.open();

        p.expect(.name);
        p.expect(.colon);
        p.type_expr();
        if (!p.at(.rparen)) {
            p.expect(.comma);
        }

        _ = p.close(m, .param);
    }

    /// TypeExpr = 'name'
    fn type_expr(p: *Parser) void {
        const m = p.open();
        p.expect(.name);
        _ = p.close(m, .expr_type);
    }

    const STMT_RECOVERY = [_]Token.Kind{.kwd_fn};
    const EXPR_FIRST = [_]Token.Kind{ .int, .kwd_true, .kwd_false, .name, .lparen };
    /// Block = '{' Stmt* '}'
    /// Stmt =
    ///   StmtExpr
    /// | StmtLet
    /// | StmtReturn
    fn block(p: *Parser) void {
        assert(p.at(.lcurly));
        const m = p.open();

        p.expect(.lcurly);
        while (!p.at(.rcurly) and !p.eof()) {
            switch (p.nth(0)) {
                .kwd_let => p.stmt_let(),
                .kwd_return => p.stmt_return(),
                else => {
                    if (p.at_any(&EXPR_FIRST)) {
                        p.stmt_expr();
                    } else {
                        if (p.at_any(&STMT_RECOVERY)) {
                            break;
                        }
                        p.advance_with_error("expected statement");
                    }
                },
            }
        }
        p.expect(.rcurly);
        _ = p.close(m, .block);
    }

    /// StmtLet = 'let' 'name' '=' Expr ';'
    fn stmt_let(p: *Parser) void {
        assert(p.at(.kwd_let));
        const m = p.open();

        p.expect(.kwd_let);
        p.expect(.name);
        p.expect(.eq);
        p.expr();
        p.expect(.semi);

        _ = p.close(m, .stmt_let);
    }

    /// StmtReturn = 'return' Expr ';'
    fn stmt_return(p: *Parser) void {
        assert(p.at(.kwd_return));
        const m = p.open();

        p.expect(.kwd_return);
        p.expr();
        p.expect(.semi);

        _ = p.close(m, .stmt_ret);
    }

    /// StmtExpr = Expr ';'
    fn stmt_expr(p: *Parser) void {
        const m = p.open();

        p.expr();
        p.expect(.semi);
        _ = p.close(m, .stmt_expr);
    }

    /// Expr =
    ///   ExprLiteral
    /// | ExprName
    /// | ExprParen
    /// | ExprBinary
    /// | ExprCall
    /// ExprBinary = Expr ('+' | '-' | '*' | '/') Expr
    /// ExprCall = Expr ArgList
    fn expr(p: *Parser) void {
        p.expr_rec(.eof);
    }
    fn expr_rec(p: *Parser, left: Token.Kind) void {
        // std.debug.print("expr_rec()\n", .{});
        var lhs = p.expr_delimited() orelse return;
        while (p.at(.lparen)) {
            const m = p.open_before(lhs);
            p.arg_list();
            lhs = p.close(m, .expr_call);
        }

        while (true) {
            const right = p.nth(0);
            if (right_binds_tighter(left, right)) {
                const m = p.open_before(lhs);
                p.advance();
                p.expr_rec(right);
                lhs = p.close(m, .expr_binary);
            } else {
                break;
            }
        }
    }

    /// ArgList = '(' Arg* ')'
    fn arg_list(p: *Parser) void {
        assert(p.at(.lparen));
        const m = p.open();

        p.expect(.lparen);
        while (!p.at(.rparen) and !p.eof()) {
            if (p.at_any(&EXPR_FIRST)) {
                p.arg();
            } else {
                break;
            }
        }
        p.expect(.rparen);

        _ = p.close(m, .arg_list);
    }

    /// Arg = Expr ','?
    fn arg(p: *Parser) void {
        const m = p.open();
        p.expr();
        if (!p.at(.rparen)) {
            p.expect(.comma);
        }
        _ = p.close(m, .arg);
    }

    fn tightness(kind: Token.Kind) ?usize {
        for ([_][]const Token.Kind{
            &.{ .plus, .minus },
            &.{ .star, .slash },
        }, 0..) |level, i| {
            for (level) |k| if (kind == k) return i;
        }
        return null;
    }

    fn right_binds_tighter(left: Token.Kind, right: Token.Kind) bool {
        const right_tightness = tightness(right) orelse return false;
        const left_tightness = tightness(left) orelse {
            assert(left == .eof);
            return true;
        };
        return right_tightness > left_tightness;
    }

    /// ExprLiteral = 'int' | 'true' | 'false'
    /// ExprName = 'name'
    /// ExprParen = '(' Expr ')'
    fn expr_delimited(p: *Parser) ?MarkClosed {
        const result = switch (p.nth(0)) {
            .kwd_true, .kwd_false, .int => blk: {
                const m = p.open();
                p.advance();
                break :blk p.close(m, .expr_lit);
            },
            .name => blk: {
                const m = p.open();
                p.advance();
                break :blk p.close(m, .expr_name);
            },
            .lparen => blk: {
                const m = p.open();
                p.expect(.lparen);
                p.expr();
                p.expect(.rparen);
                break :blk p.close(m, .expr_paren);
            },
            else => return null,
        };
        return result;
    }

    fn close(self: *Parser, m: MarkOpened, kind: Tree.Kind) MarkClosed {
        self.events.items[m.to_int()] = .{ .open = kind };
        self.events.append(self.alloc, .close) catch @panic("OOM");
        return m.to_closed();
    }

    fn advance(self: *Parser) void {
        assert(!self.eof());
        self.fuel = 256;
        self.events.append(self.alloc, .advance) catch @panic("OOM");
        self.pos += 1;
    }

    fn tokenAt(self: Parser, pos: usize) Token {
        const span = self.lexed.spans[pos];
        return .{
            .kind = self.lexed.kinds[pos],
            .src = self.src[span[0]..span[1]],
        };
    }

    fn printError(self: Parser, comptime fmt: []const u8, args: anytype) void {
        const span = self.lexed.spans[self.pos];
        var pos: u32 = 0;
        var line: u32 = 1;
        var col: u32 = 1;
        var last_nonws_linecol = [2]u32{ line, col };
        while (pos < span[0]) : (pos += 1) {
            if (self.src[pos] == '\n') {
                line += 1;
                col = 1;
            } else {
                col += 1;
            }

            const u8x6 = @Vector(6, u8);
            const ws: u8x6 = std.ascii.whitespace;
            const cs: u8x6 = @splat(self.src[pos]);
            if (@reduce(.And, cs != ws)) {
                // if (std.mem.indexOfScalar(u8, &std.ascii.whitespace, self.src[pos]) == null) {
                last_nonws_linecol = .{ line, col };
            }
        }

        std.debug.print(
            "{s}:{}:{}: error: " ++ fmt ++ "\n",
            .{ self.filepath, last_nonws_linecol[0], last_nonws_linecol[1] } ++ args,
        );
    }

    fn advance_with_error(self: *Parser, err: []const u8) void {
        const m = self.open();
        self.printError("{s}", .{err});
        self.advance();
        _ = self.close(m, .err);
    }

    fn at(self: *Parser, kind: Token.Kind) bool {
        return self.nth(0) == kind;
    }

    fn at_any(self: *Parser, kinds: []const Token.Kind) bool {
        return mem.indexOfScalar(Token.Kind, kinds, self.nth(0)) != null;
    }

    fn nth(self: *Parser, lookahead: usize) Token.Kind {
        if (self.fuel == 0) {
            @panic("parser is stuck");
        }
        self.fuel = self.fuel - 1;
        const i = self.pos + lookahead;
        return if (i >= self.lexed.kinds.len) .eof else self.lexed.kinds[i];
    }

    fn eof(self: Parser) bool {
        return self.pos >= self.lexed.kinds.len;
    }

    fn eat(self: *Parser, kind: Token.Kind) bool {
        if (self.at(kind)) {
            self.advance();
            return true;
        }
        return false;
    }

    fn expect(self: *Parser, kind: Token.Kind) void {
        if (self.eat(kind)) {
            return;
        }
        self.printError("expected {s}", .{@tagName(kind)});
    }

    fn open(self: *Parser) MarkOpened {
        const mark: MarkOpened = @enumFromInt(self.events.items.len);
        self.events.append(self.alloc, .{ .open = .err }) catch @panic("OOM");
        return mark;
    }
    fn open_before(self: *Parser, m: MarkClosed) MarkOpened {
        const mark = m.to_opened();
        self.events.insert(self.alloc, m.to_int(), .{ .open = .err }) catch @panic("OOM");
        return mark;
    }
};
