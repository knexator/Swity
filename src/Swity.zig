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
known_funcs: std.HashMap(Value, Func, Value.Context, std.hash_map.default_max_load_percentage),
main_expression: ?struct {
    func_id: Value,
    argument: Value,
} = null,

// TODO
// gpa: std.mem.Allocator,

parsing_arena: std.heap.ArenaAllocator,
per_execution_arena: std.heap.ArenaAllocator,

// TODO: maybe change to pools of Type and Func?
permanent_arena: std.heap.ArenaAllocator,

// TODO: remove
duplicated_source_arena: std.heap.ArenaAllocator,

// TODO: rename
/// keys are absolute paths
files_new: std.StringArrayHashMap(ParsedSource),

/// files brought in due to an #include
included_paths: std.ArrayList([]const u8),

pub const ParsedSource = struct {
    // TODO
    // arena: std.heap.ArenaAllocator,
    // TODO: per-file arena/pool for CST nodes (and source?)
    decls: []CST,
    // TODO: clarify ownership
    source: []const u8,

    pub fn fromText(swity: *Swity, path: []const u8, text: []const u8) ParsedSource {
        var parser: Parser = .{
            .swity = swity,
            .source_uri = path,
            .original_text_len = text.len,
            .top_level_results = .init(swity.permanent_arena.allocator()),
            .remaining_text = text,
            .arena = swity.parsing_arena.allocator(),
            .result = swity.permanent_arena.allocator(),
        };
        parser.parseAll();

        // TODO
        // _ = self.parsing_arena.reset(.retain_capacity);

        return .{
            .source = text,
            .decls = parser.top_level_results.toOwnedSlice() catch OoM(),
        };
    }

    // pub fn fromFs(gpa: std.mem.Allocator, path: []const u8) ParsedSource {
    pub fn fromFs(swity: *Swity, path: []const u8) !ParsedSource {
        // var arena: std.heap.ArenaAllocator = .init(gpa);
        const file = try std.fs.openFileAbsolute(path, .{});
        // const text = try file.readToEndAlloc(arena.allocator(), std.math.maxInt(usize));
        const text = try file.readToEndAlloc(swity.duplicated_source_arena.allocator(), std.math.maxInt(usize));

        return .fromText(swity, path, text);
    }
};

// TODO: add "and also recursive includes" to this name
pub fn reparseEverything(swity: *Swity) !void {
    swity.known_funcs.clearRetainingCapacity();
    swity.known_types.clearRetainingCapacity();
    // TODO: uncomment
    // swity.main_expression = null;

    try swity.parseEverything();
}

pub fn parseEverything(swity: *Swity) !void {
    assert(swity.known_funcs.count() == 0);
    assert(swity.known_types.count() == 0);
    // TODO: uncomment
    // assert(swity.main_expression == null);

    // TODO: mem
    var pending_files: std.fifo.LinearFifo([]const u8, .Dynamic) = .init(swity.per_execution_arena.allocator());
    {
        var it_files = swity.files_new.iterator();
        while (it_files.next()) |kv| {
            try pending_files.writeItem(kv.key_ptr.*);
        }
    }

    // std.log.debug("before starting, pending files are: {any}", .{pending_files.readableSlice(0)});
    while (pending_files.readItem()) |path| {
        // std.log.debug("doing stuff for {s}", .{path});
        const gop = try swity.files_new.getOrPut(path);
        if (!gop.found_existing) {
            // std.log.debug("loading {s} from disk", .{path});
            gop.value_ptr.* = try .fromFs(swity, path);
        }
        const asdf = gop.value_ptr.*;
        const text = asdf.source;
        for (asdf.decls) |*declaration| {
            switch (declaration.tag) {
                .data_definition => {
                    assert(declaration.children.len == 2);
                    const id = declaration.children[0].asString(text);
                    const body = declaration.children[1].asType(text, swity.permanent_arena.allocator());
                    swity.known_types.putNoClobber(id, .{ .value = body, .position = declaration }) catch OoM();
                },
                .fn_definition => {
                    assert(declaration.children.len == 4);
                    const id = declaration.children[0].asValue(text, swity.permanent_arena.allocator());
                    assert(std.meta.activeTag(id) == .literal);
                    const type_in = declaration.children[1].asType(text, swity.permanent_arena.allocator());
                    const type_out = declaration.children[2].asType(text, swity.permanent_arena.allocator());
                    const cases = declaration.children[3].asCases(text, swity.permanent_arena.allocator());
                    swity.known_funcs.putNoClobber(id, .{
                        .type_in = type_in,
                        .type_out = type_out,
                        .cases = cases,
                        .position = declaration,
                    }) catch OoM();
                },
                .include => {
                    assert(declaration.children.len == 1);
                    const filename = declaration.children[0].asString(text);
                    // TODO: memory leak
                    const new_path = swity.ownedAndNormalizedPath(std.fs.path.resolve(swity.parsing_arena.allocator(), &.{
                        path,
                        "..",
                        filename,
                    }) catch panic("TODO", .{}));
                    if (!swity.files_new.contains(new_path) and not_in_pending_files: {
                        for (pending_files.readableSlice(0)) |f| {
                            if (std.mem.eql(u8, f, new_path)) {
                                break :not_in_pending_files false;
                            }
                        } else break :not_in_pending_files true;
                    }) {
                        // std.log.debug("including {s}, which was not found", .{new_path});
                        try pending_files.writeItem(new_path);
                    }
                },
                .main_definition => {
                    assert(declaration.children.len == 2);

                    const func_id = declaration.children[0].asValue(text, swity.permanent_arena.allocator());
                    const argument = declaration.children[1].asValue(text, swity.permanent_arena.allocator());
                    // TODO
                    // assert(swity.main_expression == null);

                    swity.main_expression = .{
                        .func_id = func_id,
                        .argument = argument,
                    };
                },
                else => unreachable,
            }
        }
    }
}

/// Concrete Syntax Tree
pub const CST = struct {
    tag: enum {
        data_definition,
        fn_definition,
        main_definition,
        include,

        // keyword_data,
        // keyword_fn,
        // keyword_main,

        identifier,
        literal,
        /// multiline literal, to be interpreted as a list of chars
        eof_literal,
        /// literal without the surrounding quotes
        inner_literal,

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

    pub fn asSourceCodeString(self: CST, source: []const u8) []const u8 {
        return source[self.span.start..][0..self.span.len];
    }

    pub fn asString(self: CST, source: []const u8) []const u8 {
        return switch (self.tag) {
            .identifier, .inner_literal => source[self.span.start..][0..self.span.len],
            // removes the surrouding quotes
            .literal => source[self.span.start..][1 .. self.span.len - 1],
            else => unreachable,
        };
    }

    pub fn asType(self: CST, source: []const u8, mem: std.mem.Allocator) Type {
        switch (self.tag) {
            .identifier => {
                const str = self.asString(source);
                if (str[0] == '@') {
                    if (std.mem.eql(u8, str, "@AnyLiteral")) {
                        return .any_literal;
                    } else {
                        panic("unknown builtin type {s}", .{str});
                    }
                }
                return .{ .ref = str };
            },
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
                    case.function_id = case_cst.children[1].asValue(source, mem);
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
                        case.function_id = case_cst.children[1].asValue(source, mem);
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

    pub fn asValue(self: CST, source: []const u8, mem: std.mem.Allocator) Value {
        return switch (self.tag) {
            .literal => return .{ .literal = self.asString(source) },
            .fn_plex => {
                const result = mem.alloc(Value, self.children.len) catch OoM();
                for (result, self.children) |*dst, child| {
                    dst.* = child.asValue(source, mem);
                }
                return .{ .plex = result };
            },
            .eof_literal => {
                assert(self.children.len == 1);
                var remaining_source = self.children[0].asString(source);
                var result: Value = .{ .literal = "nil" };
                var tail: *Value = &result;
                while (remaining_source.len > 0) {
                    // hacky
                    const next_char = if (std.mem.startsWith(u8, remaining_source, "\r\n")) blk: {
                        remaining_source = remaining_source[1..];
                        break :blk "\\n";
                    } else remaining_source[0..1];

                    tail.* = .{ .plex = mem.dupe(Value, &.{
                        .{ .literal = next_char },
                        tail.*,
                    }) catch OoM() };
                    tail = &tail.plex[1];
                    remaining_source = remaining_source[1..];
                }
                return result;
            },
            // TODO: REMOVE THIS HORRIBLE HACK
            .identifier => return .{ .literal = self.asString(source) },
            else => panic("unexpected tag {any}", .{self.tag}),
        };
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
        .included_paths = .init(gpa),
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
    self.included_paths.deinit();
    // TODO: deinit each file's contents
    self.files_new.deinit();
    self.known_types.deinit();
    self.known_funcs.deinit();
    self.parsing_arena.deinit();
    self.duplicated_source_arena.deinit();
    self.permanent_arena.deinit();
    self.per_execution_arena.deinit();
}

fn ownedAndNormalizedPath(self: *Swity, untrusted_path: []const u8) []const u8 {
    // TODO: don't leak
    const result = self.permanent_arena.allocator().alloc(u8, untrusted_path.len) catch OoM();
    _ = std.mem.replace(u8, untrusted_path, "\\", "/", result);
    return result;
}

// TODO: setFileSource
pub fn addFileWithSource(self: *Swity, untrusted_path: []const u8, unowned_text: []const u8) void {
    // TODO: clarify ownership
    const path = self.ownedAndNormalizedPath(untrusted_path);
    // TODO: clarify ownership
    const text = self.duplicated_source_arena.allocator().dupe(u8, unowned_text) catch OoM();
    // self.files_new.putNoClobber(path_owned, .fromText(self, path_owned, text)) catch OoM();
    if (self.files_new.contains(path)) {
        assert(std.mem.eql(u8, self.files_new.get(path).?.source, text));
    } else {
        self.files_new.put(path, .fromText(self, path, text)) catch OoM();
    }
}

pub fn removeFile(self: *Swity, untrusted_path: []const u8) void {
    const path = self.ownedAndNormalizedPath(untrusted_path);
    assert(self.files_new.swapRemove(path));
}

pub fn addMainFile(self: *Swity, untrusted_path: []const u8) void {
    const path = self.ownedAndNormalizedPath(untrusted_path);
    const kv = self.files_new.getOrPut(path) catch OoM();
    if (kv.found_existing) {
        return;
    } else {
        kv.key_ptr.* = self.permanent_arena.allocator().dupe(u8, path) catch OoM();
        kv.value_ptr.* = ParsedSource.fromFs(self, kv.key_ptr.*) catch @panic("TODO");
    }
}

// TODO: remove
// pub fn addAllPendingTextRecursive(self: *Swity) !void {
//     var it = self.files_new.iterator();
//     while (it.next()) |kv| {
//         if (kv.value_ptr.* == null) {
//             kv.value_ptr.* = try .fromFs(self, kv.key_ptr.*);
//             break;
//         }
//     } else return;
//     // we processed a file, so let's call it again since it might have had its own includes
//     try self.addAllPendingTextRecursive();
// }

fn addReplText(self: *Swity, text: []const u8) void {
    self.files_new.putNoClobber("REPL", .fromText(self, "REPL", text)) catch OoM();
    self.reparseEverything() catch @panic("TODO");
}

pub fn executeMain(self: *Swity) !Value {
    try self.reparseEverything();
    assert(self.main_expression != null);
    try self.precompileMetaFuncs();
    self.solveAllTypes();
    self.optimizeAllFuncs();
    // std.log.debug("solved all types", .{});
    return self.apply(self.main_expression.?.func_id, self.main_expression.?.argument);
}

fn precompileMetaFuncs(self: *Swity) !void {
    var it = self.known_funcs.valueIterator();
    while (it.next()) |func| {
        if (self.findUnresolvedMetaFuncName(func.*)) |name| {
            assert(std.meta.activeTag(name) == .plex);
            assert(name.plex.len == 2);
            const cases_value = self.naiveExecute(name.plex[0], name.plex[1]);
            const compiled_func = self.funcFromCases(cases_value);
            try self.known_funcs.putNoClobber(name, compiled_func);
            break;
        }
    }
}

fn asListPlusSentinelOfValues(value: Value, mem: std.mem.Allocator) !struct { vs: []Value, sentinel: Value } {
    var remaining = value;
    var result: std.ArrayList(Value) = .init(mem);
    while (std.meta.activeTag(remaining) == .plex) {
        assert(remaining.plex.len == 2);
        try result.append(remaining.plex[0]);
        remaining = remaining.plex[1];
    }
    return .{ .vs = try result.toOwnedSlice(), .sentinel = remaining };
}

fn asListOfValues(value: Value, mem: std.mem.Allocator) ![]Value {
    const res = (try asListPlusSentinelOfValues(value, mem));
    assert(std.mem.eql(u8, res.sentinel.literal, "nil"));
    return res.vs;
}

fn funcFromCases(self: *Swity, cases_value: Value) Func {
    const S = struct {
        fn treeFromValue(value: Value, mem: std.mem.Allocator) Tree {
            assert(std.meta.activeTag(value) == .plex);
            if (value.plex.len == 2) {
                if (value.plex[0].equals(.{ .literal = "Variable" })) {
                    assert(std.meta.activeTag(value.plex[1]) == .literal);
                    return .{ .variable = .{ .name = value.plex[1].literal } };
                } else if (value.plex[0].equals(.{ .literal = "Literal" })) {
                    assert(std.meta.activeTag(value.plex[1]) == .literal);
                    return .{ .literal = value.plex[1].literal };
                }
            }
            _ = mem;
            panic("TODO: treeFromValue {any}", .{value});
        }

        fn valueFromTree(tree: Tree, mem: std.mem.Allocator) Value {
            switch (tree) {
                .literal => |lit| return .{ .literal = lit },
                .variable => panic("unexpected variable {s}", .{tree.variable.name}),
                .plex => |ps| {
                    const result = mem.alloc(Value, ps.len) catch OoM();
                    for (result, ps) |*dst, p| {
                        dst.* = valueFromTree(p, mem);
                    }
                    return .{ .plex = result };
                },
            }
        }
    };

    const cases_values = asListOfValues(cases_value, self.per_execution_arena.allocator()) catch OoM();
    const cases: []Func.Case = self.permanent_arena.allocator().alloc(Func.Case, cases_values.len) catch OoM();

    for (cases, cases_values) |*dst, case_value| {
        assert(case_value.plex.len == 4);
        const pattern_value = case_value.plex[0];
        const function_id_value = case_value.plex[1];
        const template_value = case_value.plex[2];
        const next_value = case_value.plex[3];

        dst.* = .{
            .pattern = S.treeFromValue(pattern_value, self.permanent_arena.allocator()),
            .function_id = if (function_id_value.equals(.{ .literal = "identity" })) null else S.valueFromTree(
                S.treeFromValue(
                    function_id_value,
                    self.per_execution_arena.allocator(),
                ),
                self.permanent_arena.allocator(),
            ),
            .template = S.treeFromValue(template_value, self.permanent_arena.allocator()),
            .next = if (next_value.equals(.{ .literal = "return" })) null else self.funcFromCases(next_value),
        };
    }

    return .{
        .position = undefined,
        .cases = cases,
        .type_in = .meta_unresolved,
        .type_out = .meta_unresolved,
    };
}

fn naiveExecute(self: *Swity, func_name: Value, input_value: Value) Value {
    const S = struct {
        fn matchPattern(known_vars: *std.StringHashMap(Value), pattern: Tree, value: Value) bool {
            switch (pattern) {
                .literal => |lit| return switch (value) {
                    .literal => |v| std.mem.eql(u8, lit, v),
                    else => return false,
                },
                .variable => |v| {
                    known_vars.putNoClobber(v.name, value) catch OoM();
                    return true;
                },
                .plex => |ps| switch (value) {
                    else => return false,
                    .plex => |vals| {
                        if (ps.len != vals.len) return false;
                        for (ps, vals) |p, v| {
                            if (!matchPattern(known_vars, p, v)) return false;
                        } else return true;
                    },
                },
            }
        }

        fn evaluateTemplate(mem: std.mem.Allocator, known_vars: std.StringHashMap(Value), template: Tree) Value {
            switch (template) {
                .literal => |lit| return .{ .literal = lit },
                .variable => |v| return known_vars.get(v.name) orelse panic("unknown variable {s}", .{v.name}),
                .plex => |ps| {
                    const result = mem.alloc(Value, ps.len) catch OoM();
                    for (result, ps) |*dst, p| {
                        dst.* = evaluateTemplate(mem, known_vars, p);
                    }
                    return .{ .plex = result };
                },
            }
        }
    };

    var func = self.known_funcs.get(func_name) orelse panic("TODO: nested compilation, needed for {any}", .{func_name});
    var known_vars: std.StringHashMap(Value) = .init(self.per_execution_arena.allocator());
    while (true) {
        for (func.cases) |case| {
            var maybe_vars: std.StringHashMap(Value) = .init(self.per_execution_arena.allocator());
            if (S.matchPattern(&maybe_vars, case.pattern, input_value)) {
                {
                    var it = maybe_vars.iterator();
                    while (it.next()) |kv| {
                        known_vars.putNoClobber(kv.key_ptr.*, kv.value_ptr.*) catch OoM();
                    }
                    maybe_vars.deinit();
                }

                var arg = S.evaluateTemplate(self.per_execution_arena.allocator(), known_vars, case.template);
                if (case.function_id) |f_id| {
                    arg = self.naiveExecute(f_id, arg);
                }

                if (case.next) |next| {
                    func = next;
                } else {
                    return arg;
                }
            }
        }
    }
}

fn findUnresolvedMetaFuncName(self: *Swity, func: Func) ?Value {
    for (func.cases) |case| {
        if (case.function_id) |v| {
            if (std.meta.activeTag(v) == .plex and !self.known_funcs.contains(v)) {
                return v;
            }
        }
        if (case.next) |next| {
            if (self.findUnresolvedMetaFuncName(next)) |v| {
                return v;
            }
        }
    } else return null;
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

    session.stackifyVariables(session.known_funcs.getPtr(.{ .literal = "foo" }).?);

    const foo_func = session.known_funcs.get(.{ .literal = "foo" }).?;

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

// fn getFunc(self: *Swity, func_id: Value) Func {
//     if (self.known_funcs.get(func_id)) |f| {
//         return f;
//     } else {
//         switch (func_id) {
//             .literal => |name| std.log.err("Could not find func with id {s}", .{name}),
//             .plex => |plex| {
//                 assert(plex.len == 2);
//                 const meta_name = plex[0];
//                 const meta_arg = plex[1];
//                 const cases = self.apply(meta_name, meta_arg);
//                 panic("TODO: meta compilation, for now got cases {any}", .{cases});
//             },
//         }
//         unreachable;
//     }
// }

fn getFunc(self: Swity, func_id: Value) Func {
    if (self.known_funcs.get(func_id)) |f| {
        return f;
    } else {
        std.log.err("Could not find func with id {any}", .{func_id});
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

            const bar_func = process.known_funcs.get(.{ .literal = "Bar" }).?;
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
            // TODO: remove these
            if (general == .meta_unresolved) return true;
            if (specific == .meta_unresolved) return true;

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
                .meta_unresolved => return true,
                .unresolved => unreachable,
                .any_literal => return switch (general) {
                    .any_literal => return true,
                    .meta_unresolved => return true,
                    .unresolved => unreachable,
                    .literal => return false,
                    .plex => return false,
                    .ref => |r| return isSubtypeHelper(known_types, assumptions, specific, known_types.get(r).?.value),
                    .oneof => |options| for (options) |o| {
                        if (isSubtypeHelper(known_types, assumptions, specific, o)) return true;
                    } else return false,
                },
                .literal => |l_specific| switch (general) {
                    .any_literal => return true,
                    .meta_unresolved => return true,
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
                    .any_literal => return false,
                    .meta_unresolved => return true,
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

    // TODO: remove this by computing the type of comptime functions
    if (func.type_in == .meta_unresolved or func.type_out == .meta_unresolved) return;

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
        .any_literal => return switch (value) {
            .literal => return true,
            .plex => return false,
        },
        .meta_unresolved => return true,
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

pub fn apply(self: *Swity, func_id: ?Value, original_value: Value) Value {
    // TODO: move the result to the permanent arena & uncomment this
    // defer _ = self.per_execution_arena.reset(.retain_capacity);
    const TYPE_CHECK = false;
    var active_value = original_value;
    var stack: std.ArrayList(struct {
        cur_func: Func,
        cur_bindings: []Value,

        pub fn init(swity: *Swity, id: Value) @This() {
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
    const actual = session.apply(.{ .literal = "sum" }, .{ .plex = @constCast(&[2]Value{ one, one }) });
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
    const actual = session.apply(.{ .literal = "mul" }, .{ .plex = @constCast(&[2]Value{ three, two }) });
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
    // TODO: rename to path
    source_uri: []const u8,
    arena: std.mem.Allocator,
    result: std.mem.Allocator,
    // cursor: CST.Loc,
    original_text_len: usize,
    top_level_results: std.ArrayList(CST),

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
            const id: CST = self.consumeRawSexprNew();
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
            const span_start = self.cursor() - "main".len;
            self.consumeWhitespace();
            const func_id: CST = self.consumeRawSexprNew();
            self.trimLeft();
            self.consume(":");
            self.trimLeft();
            const argument = self.consumeRawSexprNew();
            self.trimLeft();
            self.consume(";");
            const span_end = self.cursor();

            self.top_level_results.append(.{
                .tag = .main_definition,
                .span = .{
                    .uri = self.source_uri,
                    .start = span_start,
                    .len = span_end - span_start,
                },
                .children = self.result.dupe(CST, &.{
                    func_id,
                    argument,
                }) catch OoM(),
            }) catch OoM();
        } else if (self.maybeConsume("include")) {
            const span_start = self.cursor() - "include".len;
            self.consumeWhitespace();
            const filename = self.consumeIdentifierOrLiteral();
            assert(filename.tag == .literal);
            self.trimLeft();
            self.consume(";");
            const span_end = self.cursor();

            self.top_level_results.append(.{
                .tag = .include,
                .span = .{
                    .uri = self.source_uri,
                    .start = span_start,
                    .len = span_end - span_start,
                },
                .children = self.result.dupe(CST, &.{
                    filename,
                }) catch OoM(),
            }) catch OoM();
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

    fn consumeIdentifier(self: *Parser) CST {
        const result = self.consumeIdentifierOrLiteral();
        assert(result.tag == .identifier);
        return result;
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

    fn consumeInnerEof(self: *Parser) CST {
        const span_start = self.cursor();
        while (!self.maybeConsume("EOF")) {
            self.remaining_text = self.remaining_text[1..];
        }
        const span_end = self.cursor() - "EOF".len;
        return .{
            .tag = .inner_literal,
            .children = &.{},
            .span = .{
                .uri = self.source_uri,
                .start = span_start,
                .len = span_end - span_start,
            },
        };
    }

    fn consumeIdentifierOrLiteral(self: *Parser) CST {
        if (self.maybeConsume("<<EOF")) {
            const span_start = self.cursor() - "<<EOF".len;
            _ = self.maybeConsume("\r");
            self.consume("\n");
            const child = self.consumeInnerEof();
            const span_end = self.cursor();
            return .{
                .tag = .eof_literal,
                .children = self.result.dupe(CST, &.{
                    child,
                }) catch OoM(),
                .span = .{
                    .uri = self.source_uri,
                    .start = span_start,
                    .len = span_end - span_start,
                },
            };
        } else {
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
                    .function_id = .{ .literal = "mul" },
                    .template = .{ .plex = @constCast(&[_]Tree{
                        .{ .variable = .{ .name = "a" } },
                        .{ .variable = .{ .name = "b" } },
                    }) },
                    .next = .{ .cases = @constCast(&[1]Func.Case{
                        .{
                            .pattern = .{ .variable = .{ .name = "x" } },
                            .function_id = .{ .literal = "sum" },
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

        const actual = process.known_funcs.get(.{ .literal = "mul" }) orelse return error.TestUnexpectedResult;

        try S.expectEqualFuncs(expected, actual);
    }
};

pub const TypeId = []const u8;

pub const Value = union(enum) {
    literal: []const u8,
    // TODO: make this const?
    plex: []Value,

    pub fn equals(this: Value, other: Value) bool {
        return switch (this) {
            .literal => |this_literal| switch (other) {
                .literal => |other_literal| std.mem.eql(u8, this_literal, other_literal),
                else => false,
            },
            .plex => |this_ps| switch (other) {
                .plex => |other_ps| {
                    if (this_ps.len != other_ps.len) return false;
                    for (this_ps, other_ps) |a, b| {
                        if (!equals(a, b)) return false;
                    } else return true;
                },
                else => false,
            },
        };
    }

    pub const Context = struct {
        pub fn hash(_: @This(), s: Value) u32 {
            return s.hash();
        }
        pub fn eql(_: @This(), a: Value, b: Value) bool {
            return equals(a, b);
        }
    };

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

    pub fn hash(s: *const Value) u32 {
        return switch (s.*) {
            .literal => |a| std.array_hash_map.hashString(a),
            .plex => |vs| {
                var hasher = std.hash.Wyhash.init(0);
                std.hash.autoHashStrat(&hasher, vs, .DeepRecursive);
                return @truncate(hasher.final());
            },
        };
    }
};

pub const Type = union(enum) {
    unresolved,
    literal: []const u8,
    ref: TypeId,
    oneof: []const Type,
    plex: []const Type,

    any_literal,

    // TODO: remove this case
    meta_unresolved,

    pub fn format(
        self: @This(),
        comptime fmt: []const u8,
        options: std.fmt.FormatOptions,
        writer: anytype,
    ) !void {
        assert(fmt.len == 0);
        assert(std.meta.eql(options, .{}));
        switch (self) {
            .any_literal => try writer.writeAll("@AnyLiteral"),
            .unresolved, .meta_unresolved => try writer.writeAll("UNRESOLVED"),
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
        function_id: ?Value,
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
