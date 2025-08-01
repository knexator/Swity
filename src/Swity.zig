const Swity = @This();

known_types: if (TypeId == []const u8) std.StringHashMap(Type) else std.AutoHashMap(TypeId, Type),
known_funcs: if (FuncId == []const u8) std.StringHashMap(Func) else std.AutoHashMap(FuncId, Func),
main_expression: ?struct {
    func_id: FuncId,
    argument: Value,
} = null,

parsing_arena: std.heap.ArenaAllocator,
per_execution_arena: std.heap.ArenaAllocator,

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
        .per_execution_arena = .init(gpa),
        .permanent_arena = .init(gpa),
    };
}

pub fn deinit(self: *Swity) void {
    self.known_types.deinit();
    self.known_funcs.deinit();
    self.parsing_arena.deinit();
    self.duplicated_source_arena.deinit();
    self.permanent_arena.deinit();
    self.per_execution_arena.deinit();
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
    _ = self.parsing_arena.reset(.retain_capacity);
}

pub fn executeMain(self: *Swity) Value {
    assert(self.main_expression != null);
    return self.apply(self.main_expression.?.func_id, self.main_expression.?.argument);
}

fn solveTypes(self: *Swity, func: *Func) void {
    const KnownVariables = if (Variable == []const u8) std.StringHashMap(Type) else std.AutoHashMap(Variable, Type);
    const S = struct {
        fn solveTypesInner(swity: Swity, known: KnownVariables, case: *Func.Case, type_in: Type, type_out: Type) void {
            assert(bindTypes(swity, known, case.pattern, type_in));
            const type_of_argument: Type = TODO(known, case.template);
            const type_of_result: Type = if (case.function_id) |func_id| TODO(swity.known_funcs.get(func_id).?, type_of_argument) else type_of_argument;
            if (case.next) |next| {
                for (next.cases) |child_case| {
                    S.solveTypesInner(
                        self,
                        known.clone() catch OoM(),
                        case,
                        func.type_in,
                        func.type_out,
                    );
                }
            } else {
                assert(isSubtype(type_of_result, type_out));
            }
        }

        fn bindTypes(swity: Swity, known: KnownVariables, pat: Tree, @"type": Type) bool {
            switch (pat) {
                .literal => |pat_l| return swity.validValueForType(@"type", .{ .literal = pat_l }),
                .variable => |v| {
                    known.putNoClobber(v, @"type") catch OoM();
                    return true;
                },
                .plex => |pat_p| switch (@"type") {
                    else => return false,
                    .plex => |val_p| {
                        if (pat_p.len != val_p.len) return false;
                        for (pat_p, val_p) |pp, vp| {
                            if (!generateBindingsHelper(cur, pp, vp)) return false;
                        } else return true;
                    },
                },
            }
        }
    };

    assert(func.type_in != .unresolved);
    assert(func.type_out != .unresolved);
    for (func.cases) |*case| {
        S.solveTypesInner(
            self,
            .init(self.per_execution_arena.allocator()),
            case,
            func.type_in,
            func.type_out,
        );
    }
}

pub fn validValueForType(self: Swity, @"type": Type, value: Value) bool {
    switch (@"type") {
        // TODO
        // .unresolved => unreachable,
        .unresolved => return true,
        .literal => |l| return value.isTheLiteral(l),
        .ref => |r| return self.validValueForType(self.known_types.get(r).?, value),
        .oneof => |options| for (options) |o| {
            if (self.validValueForType(o, value)) return true;
        } else return false,
        .plex => |type_subparts| switch (value) {
            else => return false,
            .plex => |value_subparts| {
                for (type_subparts, value_subparts) |t, v| {
                    if (!self.validValueForType(t, v)) return false;
                } else return true;
            },
        },
    }
}

// TODO: type checking
pub fn apply(self: *Swity, func_id: ?FuncId, value: Value) Value {
    if (func_id == null) return value;
    const func = self.known_funcs.get(func_id.?) orelse panic("undefined func: {s}", .{func_id.?});
    var bindings: Bindings = .init(self.per_execution_arena.allocator());
    // TODO: when to call this?
    // defer _ = self.per_execution_arena.reset(.retain_capacity);
    return self.applyFunc(&bindings, func, value);
}

pub fn applyFunc(self: *Swity, bindings: *Bindings, func: Func, value: Value) Value {
    assert(self.validValueForType(func.type_in, value));
    for (func.cases) |case| {
        if (self.generateBindings(case.pattern, value)) |new_bindings| {
            {
                var it = new_bindings.iterator();
                while (it.next()) |entry| {
                    bindings.putNoClobber(entry.key_ptr.*, entry.value_ptr.*) catch OoM();
                }
            }
            const argument = self.fillTemplate(bindings, case.template);
            const next_value = self.apply(case.function_id, argument);
            const result = if (case.next) |next|
                self.applyFunc(bindings, next, next_value)
            else
                next_value;

            assert(self.validValueForType(func.type_out, result));
            return result;
        }
    } else unreachable;
}

fn fillTemplate(self: *Swity, bindings: *const Bindings, template: Tree) Value {
    switch (template) {
        .literal => |l| return .{ .literal = l },
        .variable => |v| return bindings.get(v).?,
        .plex => |p| {
            const result = self.per_execution_arena.allocator().alloc(Value, p.len) catch OoM();
            for (result, p) |*dst, t| {
                dst.* = self.fillTemplate(bindings, t);
            }
            return .{ .plex = result };
        },
    }
}

fn generateBindings(self: *Swity, pattern: Tree, value: Value) ?Bindings {
    const S = struct {
        fn generateBindingsHelper(cur: *Bindings, pat: Tree, val: Value) bool {
            switch (pat) {
                .literal => |pat_l| return val.isTheLiteral(pat_l),
                .variable => |v| {
                    cur.putNoClobber(v, val) catch OoM();
                    return true;
                },
                .plex => |pat_p| switch (val) {
                    else => return false,
                    .plex => |val_p| {
                        if (pat_p.len != val_p.len) return false;
                        for (pat_p, val_p) |pp, vp| {
                            if (!generateBindingsHelper(cur, pp, vp)) return false;
                        } else return true;
                    },
                },
            }
        }
    };

    var result: Bindings = .init(self.per_execution_arena.allocator());
    if (S.generateBindingsHelper(&result, pattern, value)) {
        return result;
    } else {
        // TODO: measure if this .deinit actually does something
        result.deinit();
        return null;
    }
}

test "one plus one" {
    var session: Swity = .init(std.testing.allocator);
    defer session.deinit();
    session.addText(
        \\ data Natural {
        \\      "zero",
        \\      ("succ" Natural),
        \\ }
        \\
        \\ fn sum: (Natural Natural) -> Natural {
        \\      ("zero" b) -> b;
        \\      (("succ" a) b) -> sum: (a ("succ" b));
        \\ }
    );

    const succ: Value = .{ .literal = "succ" };
    const zero: Value = .{ .literal = "zero" };
    const one: Value = .{ .plex = &.{ succ, zero } };
    const two: Value = .{ .plex = &.{ succ, one } };

    const actual = session.apply("sum", .{ .plex = &.{ one, one } });
    const expected = two;

    try std.testing.expectEqualDeep(expected, actual);
}

test "three times two" {
    var session: Swity = .init(std.testing.allocator);
    defer session.deinit();
    session.addText(
        \\ data Natural {
        \\      "zero",
        \\      ("succ" Natural),
        \\ }
        \\
        \\ fn sum: (Natural Natural) -> Natural {
        \\      ("zero" b) -> b;
        \\      (("succ" a) b) -> sum: (a ("succ" b));
        \\ }
        \\
        \\ fn mul: (Natural Natural) -> Natural {
        \\     ("zero" b) -> "zero";
        \\     (("succ" a) b) -> mul: (a b) {
        \\         x -> sum: (x b);
        \\     }
        \\ }
        \\
    );

    const succ: Value = .{ .literal = "succ" };
    const zero: Value = .{ .literal = "zero" };
    const one: Value = .{ .plex = &.{ succ, zero } };
    const two: Value = .{ .plex = &.{ succ, one } };
    const three: Value = .{ .plex = &.{ succ, two } };
    const four: Value = .{ .plex = &.{ succ, three } };
    const five: Value = .{ .plex = &.{ succ, four } };
    const six: Value = .{ .plex = &.{ succ, five } };

    const actual = session.apply("mul", .{ .plex = &.{ three, two } });
    const expected = six;

    try std.testing.expectEqualDeep(expected, actual);
}

test "main expression" {
    var session: Swity = .init(std.testing.allocator);
    defer session.deinit();
    session.addText(
        \\ data Natural {
        \\      "zero",
        \\      ("succ" Natural),
        \\ }
        \\
        \\ fn sum: (Natural Natural) -> Natural {
        \\      ("zero" b) -> b;
        \\      (("succ" a) b) -> sum: (a ("succ" b));
        \\ }
        \\
        \\ main sum: (("succ" "zero") ("succ" "zero"));
        \\
    );

    const succ: Value = .{ .literal = "succ" };
    const zero: Value = .{ .literal = "zero" };
    const one: Value = .{ .plex = &.{ succ, zero } };
    const two: Value = .{ .plex = &.{ succ, one } };

    const actual = session.executeMain();
    const expected = two;

    try std.testing.expectEqualDeep(expected, actual);
}

const Parser = struct {
    swity: *Swity,
    remaining_text: []const u8,
    arena: std.mem.Allocator,
    result: std.mem.Allocator,

    const RawSexpr = union(enum) {
        literal: []const u8,
        plex: []const RawSexpr,

        fn asValue(self: RawSexpr, mem: std.mem.Allocator) Value {
            switch (self) {
                .literal => |l| return .{ .literal = maybeLiteral(l).? },
                .plex => |p| {
                    const res = mem.alloc(Value, p.len) catch OoM();
                    for (res, p) |*dst, v| {
                        dst.* = v.asValue(mem);
                    }
                    return .{ .plex = res };
                },
            }
        }

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
        } else if (self.maybeConsume("main")) {
            assert(self.swity.main_expression == null);
            self.consumeWhitespace();
            const func_id: FuncId = self.consumeFuncId();
            self.trimLeft();
            self.consume(":");
            self.trimLeft();
            const argument = self.consumeValue();
            self.trimLeft();
            self.consume(";");
            self.swity.main_expression = .{
                .func_id = func_id,
                .argument = argument,
            };
            self.parseAll();
        } else assert(self.remaining_text.len == 0);
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
        // assert(self.maybeConsume(token));
        if (!self.maybeConsume(token)) {
            panic("expected token {s}, remaining code is {s}", .{ token, self.remaining_text });
        }
    }

    const consumeFuncId = consumeId;
    const consumeTypeId = consumeId;

    fn consumeId(self: *Parser) []const u8 {
        const raw = self.consumeRawSexpr();
        return raw.asId();
    }

    fn consumeValue(self: *Parser) Value {
        const raw = self.consumeRawSexpr();
        return raw.asValue(self.result);
    }

    fn consumeType(self: *Parser) Type {
        if (self.maybeConsume("{")) {
            var inner: std.ArrayList(Type) = .init(self.result);
            self.trimLeft();
            while (!self.maybeConsume("}")) {
                const cur = self.consumeType();
                inner.append(cur) catch OoM();
                self.trimLeft();
                self.consume(",");
                self.trimLeft();
            }
            return .{ .oneof = inner.toOwnedSlice() catch OoM() };
        } else if (self.maybeConsume("(")) {
            var inner: std.ArrayList(Type) = .init(self.result);
            self.trimLeft();
            while (!self.maybeConsume(")")) {
                const cur = self.consumeType();
                inner.append(cur) catch OoM();
                self.trimLeft();
            }
            return .{ .plex = inner.toOwnedSlice() catch OoM() };
        } else {
            const cur = self.consumeSingleWord();
            if (cur.is_literal) {
                return .{ .literal = cur.result };
            } else {
                return .{ .ref = cur.result };
            }
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
        const cases = self.consumeCases();

        return .{
            .type_in = type_in,
            .type_out = type_out,
            .cases = cases,
        };
    }

    fn consumeCases(self: *Parser) []const Func.Case {
        var inner: std.ArrayList(Func.Case) = .init(self.result);
        self.consume("{");
        self.trimLeft();
        while (!self.maybeConsume("}")) {
            const cur = self.consumeCase();
            inner.append(cur) catch OoM();
            self.trimLeft();
        }
        return inner.toOwnedSlice() catch OoM();
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
            return .{
                .pattern = pattern,
                .function_id = function_id,
                .template = template,
                .next = .{
                    .cases = self.consumeCases(),
                    .type_in = .unresolved,
                    .type_out = .unresolved,
                },
            };
        }
    }

    fn consumeSingleWord(self: *Parser) struct { result: []const u8, is_literal: bool } {
        if (self.nextIs("\"")) {
            var next_index = std.mem.indexOfScalarPos(
                u8,
                self.remaining_text,
                1,
                '"',
            ) orelse panic("unclosed \"", .{});
            while (self.remaining_text[next_index - 1] == '\\') {
                next_index = std.mem.indexOfScalarPos(
                    u8,
                    self.remaining_text,
                    next_index + 1,
                    '"',
                ) orelse panic("unclosed \"", .{});
            }
            const result = self.remaining_text[1..next_index];
            self.remaining_text = self.remaining_text[next_index + 1 ..];
            return .{ .result = result, .is_literal = true };
        } else {
            const next_index = std.mem.indexOfAny(
                u8,
                self.remaining_text,
                std.ascii.whitespace ++ "{}():;",
            ) orelse self.remaining_text.len;
            const result = self.remaining_text[0..next_index];
            self.remaining_text = self.remaining_text[next_index..];
            return .{ .result = result, .is_literal = false };
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
            // TODO NOW: remove
            var next_index = std.mem.indexOfScalarPos(
                u8,
                self.remaining_text,
                1,
                '"',
            ) orelse panic("unclosed \"", .{});
            while (self.remaining_text[next_index - 1] == '\\') {
                next_index = std.mem.indexOfScalarPos(
                    u8,
                    self.remaining_text,
                    next_index + 1,
                    '"',
                ) orelse panic("unclosed \"", .{});
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
            \\      ("error" {"negative", "overflow",}),  
            \\ }
        );

        const expected: Type = .{ .oneof = &.{
            .{ .literal = "zero" },
            .{ .plex = &.{
                .{ .literal = "succ" },
                .{ .ref = "Natural" },
            } },
            .{ .plex = &.{
                .{ .literal = "error" },
                .{ .oneof = &.{
                    .{ .literal = "negative" },
                    .{ .literal = "overflow" },
                } },
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
            \\     (("succ" a) b) -> mul: (a b) {
            \\         x -> sum: (x b);
            \\     }
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
                .{
                    .pattern = .{ .plex = &.{
                        .{ .plex = &.{
                            .{ .literal = "succ" },
                            .{ .variable = "a" },
                        } },
                        .{ .variable = "b" },
                    } },
                    .function_id = "mul",
                    .template = .{ .plex = &.{
                        .{ .variable = "a" },
                        .{ .variable = "b" },
                    } },
                    .next = .{ .cases = &.{
                        .{
                            .pattern = .{ .variable = "x" },
                            .function_id = "sum",
                            .template = .{ .plex = &.{
                                .{ .variable = "x" },
                                .{ .variable = "b" },
                            } },
                            .next = null,
                        },
                    }, .type_in = .unresolved, .type_out = .unresolved },
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

    pub fn isTheLiteral(self: Value, target: []const u8) bool {
        return switch (self) {
            else => false,
            .literal => |l| std.mem.eql(u8, l, target),
        };
    }

    pub fn format(
        self: Value,
        comptime fmt: []const u8,
        options: std.fmt.FormatOptions,
        writer: anytype,
    ) !void {
        assert(fmt.len == 0);
        assert(std.meta.eql(options, .{}));
        switch (self) {
            .literal => |l| try writer.print("\"{s}\"", .{l}),
            .plex => |p| {
                try writer.writeAll("(");
                for (p, 0..) |v, k| {
                    if (k > 0) try writer.writeAll(" ");
                    try writer.print("{any}", .{v});
                }
                try writer.writeAll(")");
            },
        }
    }
};

pub const Type = union(enum) {
    unresolved,
    literal: []const u8,
    ref: TypeId,
    oneof: []const Type,
    plex: []const Type,

    fn couldBeLiteral(self: Type, lit: []const u8, other_types: *const KnownTypes) bool {
        switch (self) {
            .unresolved => unreachable,
            // .literal => |l| std.mem.,
        }
    }
};

pub const Tree = union(enum) {
    literal: []const u8,
    variable: Variable,
    plex: []const Tree,
};

pub const Func = struct {
    type_in: Type,
    type_out: Type,
    cases: []const Case,

    pub const Cases = []const Case;

    pub const Case = struct {
        pattern: Tree,
        function_id: ?FuncId,
        template: Tree,
        next: ?Func,
    };
};

pub const Bindings = if (Variable == []const u8) std.StringHashMap(Value) else std.AutoHashMap(Variable, Value);

fn OoM() noreturn {
    panic("OoM", .{});
}

const std = @import("std");
const assert = std.debug.assert;
const panic = std.debug.panic;
