const Swity = @This();

const TypeDeclaration = struct {
    value: Type,
    position: *const CST,
};

const KnownTypes = if (TypeId == []const u8)
    std.StringHashMap(TypeDeclaration)
else
    std.AutoHashMap(TypeId, TypeDeclaration);

known_types: KnownTypes,
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

files_new: std.StringArrayHashMap(?[]CST),

/// Concrete Syntax Tree
pub const CST = struct {
    tag: enum {
        data_definition,
        fn_definition,
        main_definition,

        // keyword_data,
        // keyword_fn,
        // keyword_main,

        identifier,
        literal,

        data_oneof,
        data_plex,

        // TODO: merge data_plex and fn_plex?
        fn_plex,

        fn_cases,
        /// children: pattern, ?funcid, template, ?next_fn_cases
        fn_case,
    },
    children: []CST,
    span: struct {
        uri: []const u8,
        start: usize,
        len: usize,

        pub fn containsIndex(self: @This(), index: usize) bool {
            return self.start <= index and index < self.start + self.len;
        }
    },

    pub const Loc = struct {
        line: usize,
        column: usize,

        pub const zero: Loc = .{ .line = 0, .column = 0 };
    };

    pub fn asString(self: CST, source: []const u8) []const u8 {
        return switch (self.tag) {
            .identifier => source[self.span.start..][0..self.span.len],
            // removes the surrouding quotes
            .literal => source[self.span.start..][1 .. self.span.len - 1],
            else => unreachable,
        };
    }

    pub fn asType(self: CST, source: []const u8, mem: std.mem.Allocator) Type {
        switch (self.tag) {
            .identifier => return .{ .ref = self.asString(source) },
            .literal => return .{ .literal = self.asString(source) },
            .data_plex => {
                const result: []Type = mem.alloc(Type, self.children.len) catch OoM();
                for (result, self.children) |*dst, child| {
                    dst.* = child.asType(source, mem);
                }
                return .{ .plex = result };
            },
            .data_oneof => {
                const result: []Type = mem.alloc(Type, self.children.len) catch OoM();
                for (result, self.children) |*dst, child| {
                    dst.* = child.asType(source, mem);
                }
                return .{ .oneof = result };
            },
            else => unreachable,
        }
    }

    pub fn asCases(self: CST, source: []const u8, mem: std.mem.Allocator) []Func.Case {
        assert(self.tag == .fn_cases);
        const result: []Func.Case = mem.alloc(Func.Case, self.children.len) catch OoM();
        for (result, self.children) |*dst, case_cst| {
            assert(case_cst.tag == .fn_case);
            var case: Func.Case = undefined;
            switch (case_cst.children.len) {
                4 => {
                    case.pattern = case_cst.children[0].asTree(source, mem);
                    case.function_id = case_cst.children[1].asString(source);
                    case.template = case_cst.children[2].asTree(source, mem);
                    case.next = case_cst.children[3].asInnerFunc(source, mem);
                },
                2 => {
                    case.pattern = case_cst.children[0].asTree(source, mem);
                    case.function_id = null;
                    case.template = case_cst.children[1].asTree(source, mem);
                    case.next = null;
                },
                3 => {
                    if (case_cst.children[2].tag == .fn_cases) {
                        case.pattern = case_cst.children[0].asTree(source, mem);
                        case.function_id = null;
                        case.template = case_cst.children[1].asTree(source, mem);
                        case.next = case_cst.children[2].asInnerFunc(source, mem);
                    } else {
                        case.pattern = case_cst.children[0].asTree(source, mem);
                        case.function_id = case_cst.children[1].asString(source);
                        case.template = case_cst.children[2].asTree(source, mem);
                        case.next = null;
                    }
                },
                else => unreachable,
            }
            dst.* = case;
        }
        return result;
    }

    pub fn asTree(self: *const CST, source: []const u8, mem: std.mem.Allocator) Tree {
        switch (self.tag) {
            .identifier => return .{ .variable = .{ .name = self.asString(source) } },
            .literal => return .{ .literal = self.asString(source) },
            .fn_plex => {
                const result: []Tree = mem.alloc(Tree, self.children.len) catch OoM();
                for (result, self.children) |*dst, child| {
                    dst.* = child.asTree(source, mem);
                }
                return .{ .plex = result };
            },
            else => unreachable,
        }
    }

    pub fn asInnerFunc(self: *const CST, source: []const u8, mem: std.mem.Allocator) Func {
        return .{
            .position = self,
            .cases = self.asCases(source, mem),
            .type_in = .unresolved,
            .type_out = .unresolved,
        };
    }

    pub fn nodesAt(gpa: std.mem.Allocator, nodes: []const CST, position: usize) ![]const CST {
        var result: std.ArrayList(CST) = .init(gpa);

        var cur = nodes;
        while (true) {
            for (cur) |node| {
                if (node.span.containsIndex(position)) {
                    try result.append(node);
                    cur = node.children;
                    break;
                }
            } else break;
        }

        return try result.toOwnedSlice();
    }
};

pub fn init(gpa: std.mem.Allocator) Swity {
    return .{
        .files_new = .init(gpa),
        .known_types = .init(gpa),
        .known_funcs = .init(gpa),
        .duplicated_source_arena = .init(gpa),
        .parsing_arena = .init(gpa),
        .per_execution_arena = .init(gpa),
        .permanent_arena = .init(gpa),
    };
}

pub fn deinit(self: *Swity) void {
    self.files_new.deinit();
    self.known_types.deinit();
    self.known_funcs.deinit();
    self.parsing_arena.deinit();
    self.duplicated_source_arena.deinit();
    self.permanent_arena.deinit();
    self.per_execution_arena.deinit();
}

pub fn addFileWithSource(self: *Swity, uri: []const u8, text: []const u8) void {
    self.files_new.putNoClobber(uri, self.addText(uri, text)) catch OoM();
}

pub fn addIncludeFile(self: *Swity, uri: []const u8) void {
    const kv = self.files_new.getOrPut(uri) catch OoM();
    if (kv.found_existing) {
        return;
    } else {
        kv.key_ptr.* = self.permanent_arena.allocator().dupe(u8, uri) catch OoM();
        kv.value_ptr.* = null;
    }
}

pub fn addAllPendingTextRecursive(self: *Swity) !void {
    var it = self.files_new.iterator();
    while (it.next()) |kv| {
        if (kv.value_ptr.* == null) {
            const file = try std.fs.openFileAbsolute(kv.key_ptr.*, .{});
            const text = try file.readToEndAlloc(self.duplicated_source_arena.allocator(), std.math.maxInt(usize));
            kv.value_ptr.* = self.addText(kv.key_ptr.*, text);
            break;
        }
    } else return;

    // we processed a file, so let's call it again since it might have had its own includes
    try self.addAllPendingTextRecursive();
}

fn addText(self: *Swity, source_uri: []const u8, text: []const u8) []CST {
    var parser: Parser = .{
        .swity = self,
        .source_uri = source_uri,
        .original_text_len = text.len,
        .top_level_results = .init(self.permanent_arena.allocator()),
        .remaining_text = text,
        .arena = self.parsing_arena.allocator(),
        .result = self.permanent_arena.allocator(),
    };
    parser.parseAll();
    for (parser.top_level_results.items) |*declaration| {
        switch (declaration.tag) {
            .data_definition => {
                assert(declaration.children.len == 2);
                const id = declaration.children[0].asString(text);
                const body = declaration.children[1].asType(text, self.permanent_arena.allocator());
                self.known_types.putNoClobber(id, .{ .value = body, .position = declaration }) catch OoM();
            },
            .fn_definition => {
                assert(declaration.children.len == 4);
                const id = declaration.children[0].asString(text);
                const type_in = declaration.children[1].asType(text, self.permanent_arena.allocator());
                const type_out = declaration.children[2].asType(text, self.permanent_arena.allocator());
                const cases = declaration.children[3].asCases(text, self.permanent_arena.allocator());
                self.known_funcs.putNoClobber(id, .{
                    .type_in = type_in,
                    .type_out = type_out,
                    .cases = cases,
                    .position = declaration,
                }) catch OoM();
            },
            else => unreachable,
            // self.swity.known_funcs.putNoClobber(id, result) catch OoM();
        }
    }

    _ = self.parsing_arena.reset(.retain_capacity);

    return parser.top_level_results.toOwnedSlice() catch OoM();
}

fn addReplText(self: *Swity, text: []const u8) void {
    _ = self.addText("REPL", text);
}

pub fn executeMain(self: *Swity) !Value {
    try self.addAllPendingTextRecursive();
    assert(self.main_expression != null);
    self.solveAllTypes();
    self.optimizeAllFuncs();
    // std.log.debug("solved all types", .{});
    return self.apply(self.main_expression.?.func_id, self.main_expression.?.argument);
}

fn optimizeAllFuncs(self: *Swity) void {
    var it = self.known_funcs.valueIterator();
    while (it.next()) |f| self.stackifyVariables(f);
}

fn stackifyVariables(swity: *Swity, parent_func: *Func) void {
    const KnownVars = struct {
        data: std.StringArrayHashMap(usize),
        next_free: usize,

        pub fn newVar(self: *@This(), v: *Tree.Variable) void {
            const n = self.next_free;
            v.stack_index = n;
            self.data.putNoClobber(v.name, n) catch OoM();
            self.next_free += 1;
        }

        pub fn clone(self: @This()) @This() {
            return .{
                .data = self.data.clone() catch OoM(),
                .next_free = self.next_free,
            };
        }
    };

    const S = struct {
        fn stackifyVariablesHelper(known_vars: *KnownVars, func: *Func) void {
            func.stack_used_by_self_and_next = 0;
            for (func.cases) |*case| {
                var cur = known_vars.clone();
                addPatternVariables(&cur, &case.pattern);
                stackifyTemplateVariables(cur, &case.template);
                if (case.next) |*next| {
                    stackifyVariablesHelper(&cur, next);
                    func.stack_used_by_self_and_next = @max(func.stack_used_by_self_and_next, next.stack_used_by_self_and_next);
                } else {
                    func.stack_used_by_self_and_next = @max(func.stack_used_by_self_and_next, cur.next_free);
                }
            }
        }

        fn addPatternVariables(known_vars: *KnownVars, pattern: *Tree) void {
            switch (pattern.*) {
                .literal => {},
                .variable => |*v| known_vars.newVar(v),
                .plex => |ps| for (ps) |*p| {
                    addPatternVariables(known_vars, p);
                },
            }
        }

        fn stackifyTemplateVariables(known_vars: KnownVars, template: *Tree) void {
            switch (template.*) {
                .literal => {},
                .variable => |*v| v.stack_index = known_vars.data.get(v.name).?,
                .plex => |ps| for (ps) |*p| {
                    stackifyTemplateVariables(known_vars, p);
                },
            }
        }
    };

    defer _ = swity.parsing_arena.reset(.retain_capacity);
    var asdfasdf: KnownVars = .{ .data = .init(swity.parsing_arena.allocator()), .next_free = 0 };
    S.stackifyVariablesHelper(&asdfasdf, parent_func);
}

test "stackify variables" {
    var session: Swity = .init(std.testing.allocator);
    defer session.deinit();
    session.addReplText(
        \\ data Any {
        \\     "A",
        \\     (Any Any),
        \\ }
        \\
        \\ fn foo: Any -> Any {
        \\      (a b) -> b {
        \\          (c d) -> a {
        \\              (e f) -> (d f);
        \\          }
        \\      }
        \\      b -> b;
        \\ }
    );

    session.stackifyVariables(session.known_funcs.getPtr("foo").?);

    const foo_func = session.known_funcs.get("foo").?;

    // TODO: optimization pass to not store unused variables
    // try std.testing.expectEqual(foo_func.stack_used_by_self_and_next, 4);

    try std.testing.expectEqual(6, foo_func.stack_used_by_self_and_next);

    try std.testing.expectEqual(1, foo_func.cases[0].template.variable.stack_index.?);
    try std.testing.expectEqual(3, foo_func.cases[0].next.?.cases[0].next.?.cases[0].template.plex[0].variable.stack_index.?);
    try std.testing.expectEqual(0, foo_func.cases[1].template.variable.stack_index.?);
}

pub fn solveAllTypes(self: *Swity) void {
    {
        var it = self.known_funcs.valueIterator();
        while (it.next()) |f| self.solveTypes(f);
    }
    if (false) {
        var it = self.known_funcs.iterator();
        while (it.next()) |kv| std.log.debug("{s}: {any}", .{ kv.key_ptr.*, kv.value_ptr.* });
    }
}

fn getFunc(self: Swity, func_id: FuncId) Func {
    if (self.known_funcs.get(func_id)) |f| {
        return f;
    } else {
        std.log.err("Could not find func with id {s}", .{func_id});
        unreachable;
    }
}

// TODO: check exhaustive matches
fn solveTypes(self: *Swity, func: *Func) void {
    const KnownVariables = std.StringHashMap(Type);
    const S = struct {
        test "typing" {
            var process: Swity = .init(std.testing.allocator);
            defer process.deinit();

            process.addReplText(
                \\ data Foo ( "A" "B" )
                \\
                \\ fn Bar: Foo -> "B" {
                \\     (x y) -> x {
                \\          "A" -> "B";
                \\     }
                \\ }
                \\
            );

            process.solveAllTypes();

            const bar_func = process.known_funcs.get("Bar").?;
            const bar_inner_func = bar_func.cases[0].next.?;

            try std.testing.expectEqualDeep(bar_func.type_in, Type{ .ref = "Foo" });
            try std.testing.expectEqualDeep(bar_inner_func.type_in, Type{ .literal = "A" });
        }

        fn solveTypesInner(swity: *Swity, parent_known: KnownVariables, case: *Func.Case, type_in: Type, type_out: Type) void {
            // std.log.err("solving types inner for case {any} with type in {any}", .{ case, type_in });
            var known = parent_known.clone() catch OoM();
            if (!bindTypes(swity.*, &known, case.pattern, type_in)) {
                std.log.err("could not bind pattern {any} to type {any}", .{ case.pattern, type_in });
                unreachable;
            }
            // std.log.debug("template: {any}", .{case.template});
            const type_of_argument: Type = findTypeOfArgument(swity.permanent_arena.allocator(), known, case.template);
            // std.log.debug("type of arg: {any}", .{type_of_argument});
            const type_of_evaluated_argument: Type = if (case.function_id) |func_id|
                findTypeOfResult(swity.permanent_arena.allocator(), swity.getFunc(func_id), type_of_argument)
            else
                type_of_argument;
            // std.log.debug("type of evaluated arg: {any}", .{type_of_evaluated_argument});
            if (case.next) |*next| {
                next.type_in = type_of_evaluated_argument;
                next.type_out = type_out;
                for (next.cases) |*child_case| {
                    solveTypesInner(
                        swity,
                        known,
                        child_case,
                        type_of_evaluated_argument,
                        type_out,
                    );
                }
            } else {
                if (!isSubtype(swity.per_execution_arena.allocator(), swity.known_types, type_of_evaluated_argument, type_out)) {
                    std.log.err("expected type {any} to be a subtype of {any}", .{ type_of_evaluated_argument, type_out });
                    unreachable;
                }
            }
        }

        // TODO: return a more specific type
        fn findTypeOfResult(arena: std.mem.Allocator, func_: Func, argument_type: Type) Type {
            _ = arena;
            _ = argument_type;
            return func_.type_out;
        }

        // TODO: memory management
        // TODO: KnownVariables could be an array
        fn findTypeOfArgument(arena: std.mem.Allocator, known: KnownVariables, template: Tree) Type {
            switch (template) {
                .literal => |l| return .{ .literal = l },
                .variable => |v| return known.get(v.name) orelse panic("unknown variable {s}", .{v.name}),
                .plex => |p| {
                    const result = arena.alloc(Type, p.len) catch OoM();
                    for (result, p) |*dst, t| {
                        dst.* = findTypeOfArgument(arena, known, t);
                    }
                    return .{ .plex = result };
                },
            }
        }

        fn bindTypes(swity: Swity, known: *KnownVariables, pattern: Tree, @"type": Type) bool {
            // std.log.debug("bindTypes for pattern {any} and type {any}", .{ pattern, @"type" });
            switch (pattern) {
                .literal => |pat_l| return swity.validValueForType(@"type", .{ .literal = pat_l }),
                .variable => |v| {
                    known.putNoClobber(v.name, @"type") catch OoM();
                    return true;
                },
                .plex => |pat_p| switch (@"type") {
                    else => return false,
                    .ref => |r| return bindTypes(swity, known, pattern, swity.known_types.get(r).?.value),
                    .oneof => |options| {
                        for (options) |o| {
                            var new_known = known.clone() catch OoM();
                            if (bindTypes(swity, &new_known, pattern, o)) {
                                known.* = new_known;
                                return true;
                            } else {
                                new_known.deinit();
                            }
                        } else return false;
                    },
                    .plex => |val_p| {
                        if (pat_p.len != val_p.len) return false;
                        for (pat_p, val_p) |pp, vp| {
                            if (!bindTypes(swity, known, pp, vp)) return false;
                        } else return true;
                    },
                },
            }
        }

        test "subtype" {
            var process: Swity = .init(std.testing.allocator);
            defer process.deinit();

            process.addReplText(
                \\ data ListOfA {
                \\      "nil",
                \\      ("A" ListOfA),  
                \\ }
                \\ data ListOfAB {
                \\      "nil",
                \\      ("A" ListOfAB),
                \\      ("B" ListOfAB),
                \\ }
            );

            try std.testing.expect(isSubtype(std.testing.allocator, process.known_types, .{ .ref = "ListOfA" }, .{ .ref = "ListOfAB" }));
        }

        fn isSubtype(scratch: std.mem.Allocator, known_types: KnownTypes, specific: Type, general: Type) bool {
            var assumptions: @typeInfo(@typeInfo(@TypeOf(isSubtypeHelper)).@"fn".params[1].type.?).pointer.child = .init(scratch);
            defer assumptions.deinit();
            return isSubtypeHelper(known_types, &assumptions, specific, general);
        }

        const Assumption = struct { child: TypeId, parent: TypeId };
        fn isSubtypeHelper(known_types: KnownTypes, assumptions: *std.HashMap(
            Assumption,
            void,
            struct {
                pub fn hash(_: @This(), k: Assumption) u64 {
                    var wyhash: std.hash.Wyhash = .init(0);
                    wyhash.update(k.child);
                    wyhash.update(k.parent);
                    return wyhash.final();
                }

                pub fn eql(_: @This(), k1: Assumption, k2: Assumption) bool {
                    return std.mem.eql(u8, k1.child, k2.child) and std.mem.eql(u8, k1.parent, k2.parent);
                }
            },
            std.hash_map.default_max_load_percentage,
        ), specific: Type, general: Type) bool {
            // std.log.debug("checking isSubtype, specific {any} of general {any}", .{ specific, general });
            switch (specific) {
                .unresolved => unreachable,
                .literal => |l_specific| switch (general) {
                    .unresolved => unreachable,
                    .literal => |l_general| return std.mem.eql(u8, l_specific, l_general),
                    .plex => return false,
                    .ref => |r| return isSubtypeHelper(known_types, assumptions, specific, known_types.get(r).?.value),
                    .oneof => |options| for (options) |o| {
                        if (isSubtypeHelper(known_types, assumptions, specific, o)) return true;
                    } else return false,
                },
                .ref => |r| switch (general) {
                    else => return isSubtypeHelper(known_types, assumptions, known_types.get(r).?.value, general),
                    .ref => |rg| {
                        if (std.mem.eql(u8, r, rg))
                            return true
                        else {
                            if (assumptions.get(.{ .child = r, .parent = rg }) == null) {
                                assumptions.put(.{ .child = r, .parent = rg }, {}) catch OoM();
                                return isSubtypeHelper(known_types, assumptions, specific, known_types.get(rg).?.value);
                            } else return true;
                        }
                    },
                },
                .oneof => |options| for (options) |o| {
                    if (!isSubtypeHelper(known_types, assumptions, o, general)) return false;
                } else return true,
                .plex => |specific_parts| switch (general) {
                    .unresolved => unreachable,
                    .literal => return false,
                    .ref => |r| return isSubtypeHelper(known_types, assumptions, specific, known_types.get(r).?.value),
                    .oneof => |options| for (options) |o| {
                        if (isSubtypeHelper(known_types, assumptions, specific, o)) return true;
                    } else return false,
                    .plex => |general_parts| {
                        if (specific_parts.len != general_parts.len) return false;
                        for (specific_parts, general_parts) |s, g| {
                            if (!isSubtypeHelper(known_types, assumptions, s, g)) return false;
                        } else return true;
                    },
                },
            }
        }
    };

    assert(func.type_in != .unresolved);
    assert(func.type_out != .unresolved);
    // std.log.debug("func type in {any}", .{func.type_in});
    // std.log.debug("func type out {any}", .{func.type_out});
    for (func.cases) |*case| {
        // std.log.debug("solving inner types for case {any}", .{case.*});
        S.solveTypesInner(
            self,
            .init(self.per_execution_arena.allocator()),
            case,
            func.type_in,
            func.type_out,
        );
        // std.log.debug("after solve: {any}", .{case.*});
    }
}

// TODO: non-recursive version
pub fn validValueForType(self: Swity, @"type": Type, value: Value) bool {
    switch (@"type") {
        // TODO
        // .unresolved => unreachable,
        .unresolved => return true,
        .literal => |l| return value.isTheLiteral(l),
        .ref => |r| return self.validValueForType((self.known_types.get(r) orelse panic("unknown type {s}", .{r})).value, value),
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

pub fn apply(self: *Swity, func_id: ?FuncId, original_value: Value) Value {
    // TODO: move the result to the permanent arena & uncomment this
    // defer _ = self.per_execution_arena.reset(.retain_capacity);
    const TYPE_CHECK = false;
    var active_value = original_value;
    var stack: std.ArrayList(struct {
        cur_func: Func,
        cur_bindings: []Value,

        pub fn init(swity: *Swity, id: FuncId) @This() {
            const f = swity.known_funcs.get(id).?;
            assert(f.stack_used_by_self_and_next != std.math.maxInt(usize));
            return .{
                .cur_func = f,
                .cur_bindings = swity.per_execution_arena.allocator().alloc(Value, f.stack_used_by_self_and_next) catch OoM(),
            };
        }
    }) = .init(self.per_execution_arena.allocator());
    if (func_id == null) return active_value;
    stack.append(.init(self, func_id.?)) catch OoM();
    while (stack.pop()) |active_stack| {
        // std.log.debug("cur stack: cases {any}, active value {any}", .{ active_stack.cur_func, active_value });
        if (TYPE_CHECK) assert(self.validValueForType(active_stack.cur_func.type_in, active_value));
        for (active_stack.cur_func.cases) |case| {
            if (generateBindings(case.pattern, active_value, active_stack.cur_bindings)) {
                active_value = self.fillTemplate(active_stack.cur_bindings, case.template);
                if (case.next) |next| {
                    stack.append(.{
                        .cur_func = next,
                        .cur_bindings = active_stack.cur_bindings,
                    }) catch OoM();
                } else {
                    // TODO: check if this is actually freed
                    self.per_execution_arena.allocator().free(active_stack.cur_bindings);
                }

                if (case.function_id) |child_func_id| {
                    stack.append(.init(self, child_func_id)) catch OoM();
                }

                if (case.next == null and case.function_id == null) {
                    if (TYPE_CHECK) {
                        if (!self.validValueForType(active_stack.cur_func.type_out, active_value)) {
                            std.log.err("invalid value {any} for out type {any} while checking func cases {any}", .{ active_value, active_stack.cur_func.type_out, active_stack.cur_func.cases });
                            unreachable;
                        }
                    }
                }

                break;
            }
        } else {
            std.log.err("Ran out of cases for value {any}, and cases {any}", .{ active_value, active_stack.cur_func.cases });
            unreachable;
        }
    }
    return active_value;
}

fn fillTemplate(self: *Swity, bindings: []const Value, template: Tree) Value {
    switch (template) {
        .literal => |l| return .{ .literal = l },
        .variable => |v| return bindings[v.stack_index.?],
        .plex => |p| {
            const result = self.per_execution_arena.allocator().alloc(Value, p.len) catch OoM();
            for (result, p) |*dst, t| {
                dst.* = self.fillTemplate(bindings, t);
            }
            return .{ .plex = result };
        },
    }
}

fn generateBindings(pattern: Tree, value: Value, bindings: []Value) bool {
    switch (pattern) {
        .literal => |pat_l| return value.isTheLiteral(pat_l),
        .variable => |v| {
            bindings[v.stack_index.?] = value;
            return true;
        },
        .plex => |pat_p| switch (value) {
            else => return false,
            .plex => |val_p| {
                if (pat_p.len != val_p.len) return false;
                for (pat_p, val_p) |pp, vp| {
                    if (!generateBindings(pp, vp, bindings)) return false;
                } else return true;
            },
        },
    }
}

test "one plus one" {
    var session: Swity = .init(std.testing.allocator);
    defer session.deinit();
    session.addReplText(
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
    const one: Value = .{ .plex = @constCast(&[2]Value{ succ, zero }) };
    const two: Value = .{ .plex = @constCast(&[2]Value{ succ, one }) };

    session.optimizeAllFuncs();
    const actual = session.apply("sum", .{ .plex = @constCast(&[2]Value{ one, one }) });
    const expected = two;

    try std.testing.expectEqualDeep(expected, actual);
}

test "three times two" {
    var session: Swity = .init(std.testing.allocator);
    defer session.deinit();
    session.addReplText(
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
    const one: Value = .{ .plex = @constCast(&[2]Value{ succ, zero }) };
    const two: Value = .{ .plex = @constCast(&[2]Value{ succ, one }) };
    const three: Value = .{ .plex = @constCast(&[2]Value{ succ, two }) };
    const four: Value = .{ .plex = @constCast(&[2]Value{ succ, three }) };
    const five: Value = .{ .plex = @constCast(&[2]Value{ succ, four }) };
    const six: Value = .{ .plex = @constCast(&[2]Value{ succ, five }) };

    session.optimizeAllFuncs();
    const actual = session.apply("mul", .{ .plex = @constCast(&[2]Value{ three, two }) });
    const expected = six;

    try std.testing.expectEqualDeep(expected, actual);
}

test "main expression" {
    var session: Swity = .init(std.testing.allocator);
    defer session.deinit();
    session.addReplText(
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
    const one: Value = .{ .plex = @constCast(&[2]Value{ succ, zero }) };
    const two: Value = .{ .plex = @constCast(&[2]Value{ succ, one }) };

    const actual = session.executeMain();
    const expected = two;

    try std.testing.expectEqualDeep(expected, actual);
}

const SourceLocation = struct {
    uri: []const u8,
    line: usize,
    column: usize,
};

const Parser = struct {
    swity: *Swity,
    remaining_text: []const u8,
    source_uri: []const u8,
    arena: std.mem.Allocator,
    result: std.mem.Allocator,
    // cursor: CST.Loc,
    original_text_len: usize,
    top_level_results: std.ArrayList(CST),

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
                        return .{ .variable = .{ .name = l, .stack_index = null } };
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

    fn cursor(self: Parser) usize {
        return self.original_text_len - self.remaining_text.len;
    }

    fn parseAll(self: *Parser) void {
        self.trimLeft();
        if (self.remaining_text.len == 0) {
            return;
        } else if (self.maybeConsume("data")) {
            const span_start = self.cursor() - "data".len;
            self.consumeWhitespace();
            const id: CST = self.consumeIdentifier();
            self.trimLeft();
            const body: CST = self.consumeTypeBody();
            const span_end = self.cursor();
            self.top_level_results.append(.{
                .tag = .data_definition,
                .span = .{
                    .uri = self.source_uri,
                    .start = span_start,
                    .len = span_end - span_start,
                },
                .children = self.result.dupe(CST, &.{
                    id,
                    body,
                }) catch OoM(),
            }) catch OoM();
        } else if (self.maybeConsume("fn")) {
            const span_start = self.cursor() - "fn".len;
            self.consumeWhitespace();
            const id: CST = self.consumeIdentifier();
            self.trimLeft();
            self.consume(":");
            self.trimLeft();
            const type_in = self.consumeTypeBody();
            self.trimLeft();
            self.consume("->");
            self.trimLeft();
            const type_out = self.consumeTypeBody();
            self.trimLeft();
            const cases = self.consumeCasesNew();
            const span_end = self.cursor();
            self.top_level_results.append(.{
                .tag = .fn_definition,
                .span = .{
                    .uri = self.source_uri,
                    .start = span_start,
                    .len = span_end - span_start,
                },
                .children = self.result.dupe(CST, &.{
                    id,
                    type_in,
                    type_out,
                    cases,
                }) catch OoM(),
            }) catch OoM();
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
        } else if (self.maybeConsume("include")) {
            self.consumeWhitespace();
            const filename = self.consumeSingleLiteral();
            self.trimLeft();
            self.consume(";");

            self.swity.addIncludeFile(
                std.fs.path.resolve(self.arena, &.{
                    self.source_uri,
                    "..",
                    filename,
                }) catch panic("TODO", .{}),
            );
        } else {
            std.log.err("unexpected final text: {s}", .{self.remaining_text});
            unreachable;
        }
        self.parseAll();
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

    fn consumeIdentifier(self: *Parser) CST {
        const span_start = self.cursor();
        _ = self.consumeId();
        const span_end = self.cursor();

        return .{
            .tag = .identifier,
            .children = &.{},
            .span = .{
                .uri = self.source_uri,
                .start = span_start,
                .len = span_end - span_start,
            },
        };
    }

    fn consumeValue(self: *Parser) Value {
        if (self.maybeConsume("<<EOF")) {
            _ = self.maybeConsume("\r");
            self.consume("\n");
            var result: Value = .{ .literal = "nil" };
            var tail: *Value = &result;
            while (true) {
                if (self.maybeConsume("EOF")) {
                    return result;
                } else {
                    // hacky
                    const next_char = if (self.nextIs("\r\n")) blk: {
                        self.consume("\r");
                        break :blk "\\n";
                    } else self.remaining_text[0..1];

                    tail.* = .{ .plex = self.result.dupe(Value, &.{
                        .{ .literal = next_char },
                        tail.*,
                    }) catch OoM() };
                    tail = &tail.plex[1];
                    self.remaining_text = self.remaining_text[1..];
                }
            }
        } else {
            const raw = self.consumeRawSexpr();
            return raw.asValue(self.result);
        }
    }

    fn consumeTypeBody(self: *Parser) CST {
        if (self.maybeConsume("{")) {
            const span_start = self.cursor() - 1;
            var inner: std.ArrayList(CST) = .init(self.result);
            self.trimLeft();
            while (!self.maybeConsume("}")) {
                const cur = self.consumeTypeBody();
                inner.append(cur) catch OoM();
                self.trimLeft();
                self.consume(",");
                self.trimLeft();
            }
            const span_end = self.cursor();
            return .{
                .tag = .data_oneof,
                .children = inner.toOwnedSlice() catch OoM(),
                .span = .{
                    .uri = self.source_uri,
                    .start = span_start,
                    .len = span_end - span_start,
                },
            };
        } else if (self.maybeConsume("(")) {
            const span_start = self.cursor() - 1;
            var inner: std.ArrayList(CST) = .init(self.result);
            self.trimLeft();
            while (!self.maybeConsume(")")) {
                const cur = self.consumeTypeBody();
                inner.append(cur) catch OoM();
                self.trimLeft();
            }
            const span_end = self.cursor();
            return .{
                .tag = .data_plex,
                .children = inner.toOwnedSlice() catch OoM(),
                .span = .{
                    .uri = self.source_uri,
                    .start = span_start,
                    .len = span_end - span_start,
                },
            };
        } else {
            return self.consumeIdentifierOrLiteral();
        }
    }

    fn consumeIdentifierOrLiteral(self: *Parser) CST {
        const span_start = self.cursor();
        const is_literal = self.consumeSingleWord().is_literal;
        const span_end = self.cursor();
        return .{
            .tag = if (is_literal) .literal else .identifier,
            .children = &.{},
            .span = .{
                .uri = self.source_uri,
                .start = span_start,
                .len = span_end - span_start,
            },
        };
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

    fn consumeCasesNew(self: *Parser) CST {
        const span_start = self.cursor();
        var inner: std.ArrayList(CST) = .init(self.result);
        self.consume("{");
        self.trimLeft();
        while (!self.maybeConsume("}")) {
            const cur = self.consumeCaseNew();
            inner.append(cur) catch OoM();
            self.trimLeft();
        }
        const span_end = self.cursor();
        return .{
            .tag = .fn_cases,
            .children = inner.toOwnedSlice() catch OoM(),
            .span = .{
                .uri = self.source_uri,
                .start = span_start,
                .len = span_end - span_start,
            },
        };
    }

    fn consumeCaseNew(self: *Parser) CST {
        const span_start = self.cursor();
        const pattern = self.consumeRawSexprNew();
        self.trimLeft();
        self.consume("->");
        self.trimLeft();
        const raw_template_or_funcid = self.consumeRawSexprNew();
        self.trimLeft();
        const function_id: ?CST, const template: CST = blk: {
            if (self.nextIs("{") or self.nextIs(";")) {
                break :blk .{ null, raw_template_or_funcid };
            } else {
                self.consume(":");
                self.trimLeft();
                break :blk .{
                    raw_template_or_funcid,
                    self.consumeRawSexprNew(),
                };
            }
        };
        self.trimLeft();
        if (self.maybeConsume(";")) {
            const span_end = self.cursor();
            return .{
                .tag = .fn_case,
                .span = .{
                    .uri = self.source_uri,
                    .start = span_start,
                    .len = span_end - span_start,
                },
                .children = self.result.dupe(CST, if (function_id) |f| &.{
                    pattern,
                    f,
                    template,
                } else &.{
                    pattern,
                    template,
                }) catch OoM(),
            };
        } else {
            const next_cases = self.consumeCasesNew();
            const span_end = self.cursor();
            return .{
                .tag = .fn_case,
                .span = .{
                    .uri = self.source_uri,
                    .start = span_start,
                    .len = span_end - span_start,
                },
                .children = self.result.dupe(CST, if (function_id) |f| &.{
                    pattern,
                    f,
                    template,
                    next_cases,
                } else &.{
                    pattern,
                    template,
                    next_cases,
                }) catch OoM(),
            };
        }
    }

    fn consumeRawSexprNew(self: *Parser) CST {
        if (self.maybeConsume("(")) {
            const span_start = self.cursor() - 1;
            var inner: std.ArrayList(CST) = .init(self.result);
            self.trimLeft();
            while (!self.maybeConsume(")")) {
                const cur = self.consumeRawSexprNew();
                inner.append(cur) catch OoM();
                self.trimLeft();
            }
            const span_end = self.cursor();
            return .{
                .tag = .fn_plex,
                .children = inner.toOwnedSlice() catch OoM(),
                .span = .{
                    .uri = self.source_uri,
                    .start = span_start,
                    .len = span_end - span_start,
                },
            };
        } else {
            return self.consumeIdentifierOrLiteral();
        }
    }

    fn consumeCases(self: *Parser) []Func.Case {
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

    fn consumeSingleLiteral(self: *Parser) []const u8 {
        const result = self.consumeSingleWord();
        assert(result.is_literal);
        return result.result;
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
                std.ascii.whitespace ++ "{}():;,",
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
            .top_level_results = .init(process.permanent_arena.allocator()),
            .swity = &process,
            .source_uri = "REPL",
            .remaining_text = "",
            .original_text_len = 0,
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

        process.addReplText(
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

        const actual = (process.known_types.get("Natural") orelse return error.TestUnexpectedResult).value;

        try std.testing.expectEqualDeep(expected, actual);
    }

    test "parse func" {
        const S = struct {
            pub fn expectEqualFuncs(expected: Func, actual: Func) error{TestExpectedEqual}!void {
                try std.testing.expectEqualDeep(expected.type_in, actual.type_in);
                try std.testing.expectEqualDeep(expected.type_out, actual.type_out);
                try std.testing.expectEqual(expected.cases.len, actual.cases.len);
                for (expected.cases, actual.cases) |e, a| {
                    try std.testing.expectEqualDeep(e.function_id, a.function_id);
                    try std.testing.expectEqualDeep(e.pattern, a.pattern);
                    try std.testing.expectEqualDeep(e.template, a.template);
                    if (e.next) |e_next| {
                        std.testing.expect(a.next != null) catch return error.TestExpectedEqual;
                        try expectEqualFuncs(e_next, a.next.?);
                    } else {
                        std.testing.expect(a.next == null) catch return error.TestExpectedEqual;
                    }
                }
            }
        };

        var process: Swity = .init(std.testing.allocator);
        defer process.deinit();

        process.addReplText(
            \\ fn mul: (Natural Natural) -> Natural {
            \\     ("zero" b) -> "zero";
            \\     (("succ" a) b) -> mul: (a b) {
            \\         x -> sum: (x b);
            \\     }
            \\ }
        );

        const expected: Func = .{
            .position = undefined,
            .type_in = .{ .plex = &.{
                .{ .ref = "Natural" },
                .{ .ref = "Natural" },
            } },
            .type_out = .{ .ref = "Natural" },
            .cases = @constCast(&[2]Func.Case{
                .{
                    .pattern = .{ .plex = @constCast(&[_]Tree{
                        .{ .literal = "zero" },
                        .{ .variable = .{ .name = "b" } },
                    }) },
                    .function_id = null,
                    .template = .{ .literal = "zero" },
                    .next = null,
                },
                .{
                    .pattern = .{ .plex = @constCast(&[_]Tree{
                        .{ .plex = @constCast(&[_]Tree{
                            .{ .literal = "succ" },
                            .{ .variable = .{ .name = "a" } },
                        }) },
                        .{ .variable = .{ .name = "b" } },
                    }) },
                    .function_id = "mul",
                    .template = .{ .plex = @constCast(&[_]Tree{
                        .{ .variable = .{ .name = "a" } },
                        .{ .variable = .{ .name = "b" } },
                    }) },
                    .next = .{ .cases = @constCast(&[1]Func.Case{
                        .{
                            .pattern = .{ .variable = .{ .name = "x" } },
                            .function_id = "sum",
                            .template = .{ .plex = @constCast(&[_]Tree{
                                .{ .variable = .{ .name = "x" } },
                                .{ .variable = .{ .name = "b" } },
                            }) },
                            .next = null,
                        },
                    }), .type_in = .unresolved, .type_out = .unresolved, .position = undefined },
                },
            }),
        };

        const actual = process.known_funcs.get("mul") orelse return error.TestUnexpectedResult;

        try S.expectEqualFuncs(expected, actual);
    }
};

pub const TypeId = []const u8;
pub const FuncId = []const u8;

pub const Value = union(enum) {
    literal: []const u8,
    // TODO: make this const?
    plex: []Value,

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

    pub fn format(
        self: @This(),
        comptime fmt: []const u8,
        options: std.fmt.FormatOptions,
        writer: anytype,
    ) !void {
        assert(fmt.len == 0);
        assert(std.meta.eql(options, .{}));
        switch (self) {
            .unresolved => try writer.writeAll("UNRESOLVED"),
            .literal => |l| try writer.print("\"{s}\"", .{l}),
            .ref => |r| try writer.writeAll(r),
            .oneof => |os| {
                try writer.writeAll("{\n");
                for (os) |o| {
                    try writer.writeAll("\t");
                    try o.format(fmt, options, writer);
                    try writer.writeAll(",\n");
                }
                try writer.writeAll("}");
            },
            .plex => |ps| {
                try writer.writeAll("(");
                for (ps) |p| {
                    try p.format(fmt, options, writer);
                    try writer.writeAll(" ");
                }
                try writer.writeAll(")");
            },
        }
    }
};

pub const Tree = union(enum) {
    pub const Variable = struct { name: []const u8, stack_index: ?usize = null };

    literal: []const u8,
    variable: Variable,
    // TODO: make const?
    plex: []Tree,

    pub fn format(
        self: @This(),
        comptime fmt: []const u8,
        options: std.fmt.FormatOptions,
        writer: anytype,
    ) !void {
        assert(fmt.len == 0);
        assert(std.meta.eql(options, .{}));
        switch (self) {
            .literal => |l| try writer.print("\"{s}\"", .{l}),
            .variable => |v| try writer.writeAll(v.name),
            .plex => |ps| {
                try writer.writeAll("(");
                for (ps) |p| {
                    try p.format(fmt, options, writer);
                    try writer.writeAll(" ");
                }
                try writer.writeAll(")");
            },
        }
    }
};

pub const Func = struct {
    type_in: Type,
    type_out: Type,
    cases: []Case,

    // TODO: should be undefined
    stack_used_by_self_and_next: usize = std.math.maxInt(usize),

    position: *const CST,

    pub const Case = struct {
        pattern: Tree,
        function_id: ?FuncId,
        template: Tree,
        next: ?Func,

        pub fn format(
            self: Case,
            comptime fmt: []const u8,
            options: std.fmt.FormatOptions,
            writer: std.io.AnyWriter,
            // writer: anytype,
        ) !void {
            std.debug.assert(std.mem.eql(u8, fmt, ""));
            std.debug.assert(std.meta.eql(options, .{}));
            if (self.function_id) |func_id| {
                try writer.print("{any} -> {s}: {any}", .{ self.pattern, func_id, self.template });
            } else {
                try writer.print("{any} -> {any}", .{ self.pattern, self.template });
            }
            if (self.next) |next| {
                try writer.print(" {any}", .{next});
            } else {
                try writer.writeAll(";");
            }
        }
    };

    pub fn format(
        self: Func,
        comptime fmt: []const u8,
        options: std.fmt.FormatOptions,
        writer: std.io.AnyWriter,
    ) !void {
        std.debug.assert(std.mem.eql(u8, fmt, ""));
        std.debug.assert(std.meta.eql(options, .{}));
        try writer.print("{any} -> {any} ", .{ self.type_in, self.type_out });
        try writer.writeAll("{\n");
        for (self.cases) |case| {
            try writer.print("{any}\n", .{case});
        }
        try writer.writeAll("}");
    }
};

fn OoM() noreturn {
    panic("OoM", .{});
}

const std = @import("std");
const assert = std.debug.assert;
const panic = std.debug.panic;
