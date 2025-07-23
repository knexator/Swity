const Swity = @This();

comptime {
    assert(TypeId == []const u8);
    assert(FuncId == []const u8);
}
known_types: std.StringHashMap(Type),
known_funcs: std.StringHashMap(Func),

parsing_arena: std.heap.ArenaAllocator,

// TODO: maybe change to pools of Type and Func?
permanent_arena: std.heap.ArenaAllocator,

// TODO: remove
duplicated_source_arena: std.heap.ArenaAllocator,

pub fn init(gpa: std.mem.Allocator) Swity {
    return .{
        .known_types = .init(gpa),
        .known_funcs = .init(gpa),
        .duplicated_source_arena = .init(gpa),
        .parsing_arena = .init(gpa),
        .permanent_arena = .init(gpa),
    };
}

pub fn deinit(self: *Swity) void {
    self.known_types.deinit();
    self.known_funcs.deinit();
    self.parsing_arena.deinit();
    self.duplicated_source_arena.deinit();
    self.permanent_arena.deinit();
}

pub fn addText(self: *Swity, text: []const u8) void {
    const owned_text = self.duplicated_source_arena.allocator().dupe(u8, text) catch OoM();

    var parser: Parser = .{
        .swity = self,
        .remaining_text = owned_text,
        .arena = self.parsing_arena.allocator(),
        .result = self.permanent_arena.allocator(),
    };
    parser.parseAll();
}

const Parser = struct {
    swity: *Swity,
    remaining_text: []const u8,
    arena: std.mem.Allocator,
    result: std.mem.Allocator,

    const RawSexpr = union(enum) {
        literal: []const u8,
        plex: []const RawSexpr,

        fn asTree(self: RawSexpr, mem: std.mem.Allocator) Tree {
            switch (self) {
                .literal => |l| {
                    if (maybeLiteral(l)) |r| {
                        return .{ .literal = r };
                    } else {
                        return .{ .variable = l };
                    }
                },
                .plex => |p| {
                    const res = mem.alloc(Tree, p.len) catch OoM();
                    for (res, p) |*dst, v| {
                        dst.* = v.asTree(mem);
                    }
                    return .{ .plex = res };
                },
            }
        }

        fn asType(self: RawSexpr, mem: std.mem.Allocator) Type {
            switch (self) {
                .literal => |l| {
                    if (maybeLiteral(l)) |r| {
                        return .{ .literal = r };
                    } else {
                        return .{ .ref = l };
                    }
                },
                .plex => |p| {
                    const res = mem.alloc(Type, p.len) catch OoM();
                    for (res, p) |*dst, v| {
                        dst.* = v.asType(mem);
                    }
                    return .{ .plex = res };
                },
            }
        }

        fn maybeLiteral(l: []const u8) ?[]const u8 {
            if (l[0] == '"') return l[1 .. l.len - 1];
            return null;
        }

        fn asId(self: RawSexpr) []const u8 {
            switch (self) {
                else => unreachable,
                .literal => |l| {
                    assert(maybeLiteral(l) == null);
                    return l;
                },
            }
        }
    };

    fn parseAll(self: *Parser) void {
        self.trimLeft();

        if (self.maybeConsume("data")) {
            self.consumeWhitespace();
            const id: TypeId = self.consumeTypeId();
            self.trimLeft();
            const result: Type = self.consumeType();
            self.swity.known_types.putNoClobber(id, result) catch OoM();
            self.parseAll();
        } else if (self.maybeConsume("fn")) {
            self.consumeWhitespace();
            const id: FuncId = self.consumeFuncId();
            self.trimLeft();
            const result: Func = self.consumeFunc();
            self.swity.known_funcs.putNoClobber(id, result) catch OoM();
            self.parseAll();
        }
    }

    fn nextIs(self: *Parser, token: []const u8) bool {
        return std.mem.startsWith(u8, self.remaining_text, token);
    }

    fn maybeConsume(self: *Parser, token: []const u8) bool {
        if (std.mem.startsWith(u8, self.remaining_text, token)) {
            self.remaining_text = self.remaining_text[token.len..];
            return true;
        } else return false;
    }

    fn consume(self: *Parser, token: []const u8) void {
        assert(self.maybeConsume(token));
    }

    const consumeFuncId = consumeId;
    const consumeTypeId = consumeId;

    fn consumeId(self: *Parser) []const u8 {
        const raw = self.consumeRawSexpr();
        return raw.asId();
    }

    fn consumeType(self: *Parser) Type {
        if (self.maybeConsume("{")) {
            var inner: std.ArrayList(Type) = .init(self.result);
            self.trimLeft();
            while (!self.maybeConsume("}")) {
                const cur = self.consumeRawSexpr().asType(self.result);
                inner.append(cur) catch OoM();
                self.trimLeft();
                self.consume(",");
                self.trimLeft();
            }
            return .{ .plex = inner.toOwnedSlice() catch OoM() };
        } else {
            return self.consumeRawSexpr().asType(self.result);
        }
    }

    fn consumeFunc(self: *Parser) Func {
        self.consume(":");
        self.trimLeft();

        const type_in = self.consumeType();
        self.trimLeft();
        self.consume("->");
        self.trimLeft();
        const type_out = self.consumeType();
        self.trimLeft();

        var inner: std.ArrayList(Func.Case) = .init(self.result);
        self.consume("{");
        self.trimLeft();
        while (!self.maybeConsume("}")) {
            const cur = self.consumeCase();
            inner.append(cur) catch OoM();
            self.trimLeft();
        }
        return .{
            .type_in = type_in,
            .type_out = type_out,
            .cases = inner.toOwnedSlice() catch OoM(),
        };
    }

    fn consumeCase(self: *Parser) Func.Case {
        const pattern = self.consumeRawSexpr().asTree(self.result);
        self.trimLeft();
        self.consume("->");
        self.trimLeft();
        const raw_template_or_funcid = self.consumeRawSexpr();
        self.trimLeft();
        const function_id: ?FuncId, const template: Tree = blk: {
            if (self.nextIs("{") or self.nextIs(";")) {
                break :blk .{ null, raw_template_or_funcid.asTree(self.result) };
            } else {
                self.consume(":");
                self.trimLeft();
                break :blk .{
                    raw_template_or_funcid.asId(),
                    self.consumeRawSexpr().asTree(self.result),
                };
            }
        };
        self.trimLeft();
        if (self.maybeConsume(";")) {
            return .{
                .pattern = pattern,
                .function_id = function_id,
                .template = template,
                .next = null,
            };
        } else {
            @panic("TODO");
        }
    }

    fn consumeRawSexpr(self: *Parser) RawSexpr {
        if (self.maybeConsume("(")) {
            var inner: std.ArrayList(RawSexpr) = .init(self.arena);
            self.trimLeft();
            while (!self.maybeConsume(")")) {
                inner.append(self.consumeRawSexpr()) catch OoM();
                self.trimLeft();
            }
            return .{ .plex = inner.toOwnedSlice() catch OoM() };
        } else if (self.nextIs("\"")) {
            var next_index = std.mem.indexOfScalarPos(
                u8,
                self.remaining_text,
                1,
                '"',
            ) orelse std.debug.panic("unclosed \"", .{});
            while (self.remaining_text[next_index - 1] == '\\') {
                next_index = std.mem.indexOfScalarPos(
                    u8,
                    self.remaining_text,
                    next_index + 1,
                    '"',
                ) orelse std.debug.panic("unclosed \"", .{});
            }
            const result: RawSexpr = .{ .literal = self.remaining_text[0 .. next_index + 1] };
            self.remaining_text = self.remaining_text[next_index + 1 ..];
            return result;
        } else {
            const next_index = std.mem.indexOfAny(
                u8,
                self.remaining_text,
                std.ascii.whitespace ++ "{}():;",
            ) orelse self.remaining_text.len;
            const result: RawSexpr = .{ .literal = self.remaining_text[0..next_index] };
            self.remaining_text = self.remaining_text[next_index..];
            return result;
        }
    }

    fn consumeWhitespace(self: *Parser) void {
        const old_len = self.remaining_text.len;
        self.trimLeft();
        assert(old_len != self.remaining_text.len);
    }

    fn trimLeft(self: *Parser) void {
        self.remaining_text = std.mem.trimLeft(u8, self.remaining_text, &std.ascii.whitespace);
        if (self.nextIs("//")) {
            if (std.mem.indexOfScalar(u8, self.remaining_text, '\n')) |line_end| {
                self.remaining_text = self.remaining_text[(line_end + 1)..];
            } else {
                self.remaining_text = self.remaining_text[self.remaining_text.len..];
            }
            self.trimLeft();
        }
    }

    test "parse raw" {
        var process: Swity = .init(std.testing.allocator);
        defer process.deinit();

        var parser: Parser = .{
            .swity = &process,
            .remaining_text = "",
            .arena = process.parsing_arena.allocator(),
            .result = process.permanent_arena.allocator(),
        };

        {
            parser.remaining_text = "foo";
            const expected: RawSexpr = .{ .literal = "foo" };
            const actual = parser.consumeRawSexpr();
            try std.testing.expectEqualDeep(expected, actual);
            try std.testing.expectEqualStrings("", parser.remaining_text);
        }

        {
            parser.remaining_text = "foo)";
            const expected: RawSexpr = .{ .literal = "foo" };
            const actual = parser.consumeRawSexpr();
            try std.testing.expectEqualDeep(expected, actual);
            try std.testing.expectEqualStrings(")", parser.remaining_text);
        }

        {
            parser.remaining_text = "foo:";
            const expected: RawSexpr = .{ .literal = "foo" };
            const actual = parser.consumeRawSexpr();
            try std.testing.expectEqualDeep(expected, actual);
            try std.testing.expectEqualStrings(":", parser.remaining_text);
        }

        {
            parser.remaining_text = "(foo)";
            const expected: RawSexpr = .{ .plex = &.{
                .{ .literal = "foo" },
            } };
            const actual = parser.consumeRawSexpr();
            try std.testing.expectEqualDeep(expected, actual);
            try std.testing.expectEqualStrings("", parser.remaining_text);
        }
    }

    test "parse data" {
        var process: Swity = .init(std.testing.allocator);
        defer process.deinit();

        process.addText(
            \\ data Natural {
            \\      "zero",
            \\      ("succ" Natural),
            \\ }
        );

        const expected: Type = .{ .plex = &.{
            .{ .literal = "zero" },
            .{ .plex = &.{
                .{ .literal = "succ" },
                .{ .ref = "Natural" },
            } },
        } };

        const actual = process.known_types.get("Natural") orelse return error.TestUnexpectedResult;

        try std.testing.expectEqualDeep(expected, actual);
    }

    test "parse func" {
        var process: Swity = .init(std.testing.allocator);
        defer process.deinit();

        process.addText(
            \\ fn mul: (Natural Natural) -> Natural {
            \\     ("zero" b) -> "zero";
            \\     // (("succ" a) b) -> mul: (a b) {
            \\     //     x -> sum: (x b);
            \\     // }
            \\ }
        );

        const expected: Func = .{
            .type_in = .{ .plex = &.{
                .{ .ref = "Natural" },
                .{ .ref = "Natural" },
            } },
            .type_out = .{ .ref = "Natural" },
            .cases = &.{
                .{
                    .pattern = .{ .plex = &.{
                        .{ .literal = "zero" },
                        .{ .variable = "b" },
                    } },
                    .function_id = null,
                    .template = .{ .literal = "zero" },
                    .next = null,
                },
            },
        };

        const actual = process.known_funcs.get("mul") orelse return error.TestUnexpectedResult;

        try std.testing.expectEqualDeep(expected, actual);
    }
};

pub const TypeId = []const u8;
pub const FuncId = []const u8;
pub const Variable = []const u8;

pub const Value = union(enum) {
    literal: []const u8,
    plex: []const Value,
};

pub const Type = union(enum) {
    literal: []const u8,
    ref: TypeId,
    plex: []const Type,
};

pub const Tree = union(enum) {
    literal: []const u8,
    variable: Variable,
    plex: []const Tree,
};

pub const Func = struct {
    type_in: Type,
    type_out: Type,
    cases: Cases,

    pub const Cases = []const Case;

    pub const Case = struct {
        pattern: Tree,
        function_id: ?FuncId,
        template: Tree,
        next: ?Cases,
    };
};

pub const Bindings = std.AutoHashMap(Variable, Value);

// pub fn match(tree: Tree, value: Value) ?Bindings {
//     const bindings : Bindings = .init(gpa)
// }

fn OoM() noreturn {
    std.debug.panic("OoM", .{});
}

const std = @import("std");
const assert = std.debug.assert;
