pub fn run(gpa: std.mem.Allocator) !void {
    var transport: lsp.TransportOverStdio = .init(std.io.getStdIn(), std.io.getStdOut());

    var handler: Handler = .init(gpa);
    defer handler.deinit();

    try lsp.basic_server.run(
        gpa,
        transport.any(),
        &handler,
        std.log.err,
    );
}

test "hover definition" {
    var handler: Handler = .init(std.testing.allocator);
    defer handler.deinit();

    var per_call_arena: std.heap.ArenaAllocator = .init(std.testing.allocator);

    _ = handler.initialize(per_call_arena.allocator(), .{
        .capabilities = .{
            .general = .{
                .positionEncodings = &.{
                    .@"utf-8",
                },
            },
        },
    });
    _ = per_call_arena.reset(.free_all);

    const source: []const u8 =
        \\data Foo {
        \\    "1",
        \\    (Foo "2"),
        \\}
    ;
    try handler.@"textDocument/didOpen"(
        per_call_arena.allocator(),
        .{ .textDocument = .{
            .uri = "file:///C:/test_file.swt",
            .languageId = "swity",
            .version = 1,
            .text = source,
        } },
    );
    _ = per_call_arena.reset(.free_all);
    const response = try handler.@"textDocument/hover"(
        per_call_arena.allocator(),
        .{ .textDocument = .{ .uri = "file:///C:/test_file.swt" }, .position = .{
            .line = 2,
            .character = 5,
        } },
    );
    _ = per_call_arena.reset(.free_all);

    try handler.@"textDocument/didClose"(
        per_call_arena.allocator(),
        .{ .textDocument = .{
            .uri = "file:///C:/test_file.swt",
        } },
    );
    _ = per_call_arena.reset(.free_all);

    try std.testing.expect(response != null);
    try std.testing.expectEqualStrings(response.?.contents.MarkupContent.value,
        \\```swt
        \\data Foo {
        \\    "1",
        \\    (Foo "2"),
        \\}
        \\```
    );
}

pub const Handler = struct {
    allocator: std.mem.Allocator,
    session: Swity,
    /// The LSP protocol specifies position inside a text document using a line and character pair.
    /// This field stores which encoding is used for the character value (UTF-8, UTF-16, UTF-32).
    ///
    /// https://microsoft.github.io/language-server-protocol/specifications/specification-current/#textDocuments
    offset_encoding: lsp.offsets.Encoding,

    fn init(allocator: std.mem.Allocator) Handler {
        return .{
            .allocator = allocator,
            .session = .init(allocator),
            // The default position encoding is UTF-16.
            // The agreed upon encoding between server client is actually decided during `initialize`.
            .offset_encoding = .@"utf-16",
        };
    }

    fn deinit(handler: *Handler) void {
        handler.session.deinit();
        handler.* = undefined;

        // TODO
        // var file_it = handler.files.iterator();
        // while (file_it.next()) |entry| {
        //     handler.allocator.free(entry.key_ptr.*);
        //     handler.allocator.free(entry.value_ptr.*);
        // }

        // handler.files.deinit(handler.allocator);

        // handler.* = undefined;
    }

    /// https://microsoft.github.io/language-server-protocol/specifications/specification-current/#initialize
    pub fn initialize(
        handler: *Handler,
        _: std.mem.Allocator,
        request: lsp.types.InitializeParams,
    ) lsp.types.InitializeResult {
        std.log.debug("Received 'initialize' message", .{});

        if (request.clientInfo) |client_info| {
            std.log.info("The client is '{s}' ({s})", .{ client_info.name, client_info.version orelse "unknown version" });
        }

        // Specifies which features are supported by the client/editor.
        const client_capabilities: lsp.types.ClientCapabilities = request.capabilities;

        // Pick the client's favorite character offset encoding.
        if (client_capabilities.general) |general| {
            for (general.positionEncodings orelse &.{}) |encoding| {
                handler.offset_encoding = switch (encoding) {
                    .@"utf-8" => .@"utf-8",
                    .@"utf-16" => .@"utf-16",
                    .@"utf-32" => .@"utf-32",
                    .custom_value => continue,
                };
                break;
            }
        }

        // Specifies which features are supported by the language server.
        const server_capabilities: lsp.types.ServerCapabilities = .{
            .positionEncoding = switch (handler.offset_encoding) {
                .@"utf-8" => .@"utf-8",
                .@"utf-16" => .@"utf-16",
                .@"utf-32" => .@"utf-32",
            },
            .textDocumentSync = .{
                .TextDocumentSyncOptions = .{
                    .openClose = true,
                    // TODO: change to Incremental
                    .change = .Full,
                },
            },
            .hoverProvider = .{ .bool = true },
            .definitionProvider = .{ .bool = true },
        };

        // Tries to validate that our server capabilities are actually implemented.
        if (@import("builtin").mode == .Debug) {
            lsp.basic_server.validateServerCapabilities(Handler, server_capabilities);
        }

        return .{
            .serverInfo = .{
                .name = "Swity LSP",
                .version = "0.1.0",
            },
            .capabilities = server_capabilities,
        };
    }

    /// https://microsoft.github.io/language-server-protocol/specifications/specification-current/#initialized
    pub fn initialized(
        _: *Handler,
        _: std.mem.Allocator,
        _: lsp.types.InitializedParams,
    ) void {
        std.log.debug("Received 'initialized' notification", .{});
    }

    /// https://microsoft.github.io/language-server-protocol/specifications/specification-current/#shutdown
    pub fn shutdown(
        _: *Handler,
        _: std.mem.Allocator,
        _: void,
    ) ?void {
        std.log.debug("Received 'shutdown' request", .{});
        return null;
    }

    /// https://microsoft.github.io/language-server-protocol/specifications/specification-current/#exit
    /// The `lsp.basic_server.run` function will automatically return after this function completes.
    pub fn exit(
        _: *Handler,
        _: std.mem.Allocator,
        _: void,
    ) void {
        std.log.debug("Received 'exit' notification", .{});
    }

    /// https://microsoft.github.io/language-server-protocol/specifications/specification-current/#textDocument_didOpen
    pub fn @"textDocument/didOpen"(
        self: *Handler,
        arena: std.mem.Allocator,
        notification: lsp.types.DidOpenTextDocumentParams,
    ) !void {
        std.log.debug("Received 'textDocument/didOpen' notification", .{});

        std.log.debug("opening {s}", .{notification.textDocument.uri});

        self.session.addFileWithSource(
            try pathFromUri(notification.textDocument.uri, arena),
            notification.textDocument.text,
        );
        try self.session.reparseEverything();
    }

    /// https://microsoft.github.io/language-server-protocol/specifications/specification-current/#textDocument_didChange
    pub fn @"textDocument/didChange"(
        self: *Handler,
        arena: std.mem.Allocator,
        notification: lsp.types.DidChangeTextDocumentParams,
    ) !void {
        std.log.debug("Received 'textDocument/didChange' notification", .{});

        const path = try pathFromUri(notification.textDocument.uri, arena);

        std.log.debug("changing {s}", .{path});

        const current_text = (self.session.files_new.get(path) orelse {
            std.log.warn("Modifying non existent Document: '{s}'", .{notification.textDocument.uri});
            return;
        }).source;

        var buffer: std.ArrayListUnmanaged(u8) = .empty;
        errdefer buffer.deinit(self.allocator);

        try buffer.appendSlice(self.allocator, current_text);

        for (notification.contentChanges) |content_change| {
            switch (content_change) {
                .literal_1 => |change| {
                    buffer.clearRetainingCapacity();
                    try buffer.appendSlice(self.allocator, change.text);
                },
                .literal_0 => |change| {
                    const loc = lsp.offsets.rangeToLoc(buffer.items, change.range, self.offset_encoding);
                    try buffer.replaceRange(self.allocator, loc.start, loc.end - loc.start, change.text);
                },
            }
        }

        const new_text = try buffer.toOwnedSlice(self.allocator);

        self.session.removeFile(path);
        self.session.addFileWithSource(path, new_text);
        try self.session.reparseEverything();
    }

    /// https://microsoft.github.io/language-server-protocol/specifications/specification-current/#textDocument_didClose
    pub fn @"textDocument/didClose"(
        self: *Handler,
        arena: std.mem.Allocator,
        notification: lsp.types.DidCloseTextDocumentParams,
    ) !void {
        std.log.debug("Received 'textDocument/didClose' notification", .{});

        const path = try pathFromUri(notification.textDocument.uri, arena);

        std.log.debug("closing {s}", .{path});

        self.session.removeFile(path);
        try self.session.reparseEverything();
    }

    fn sourceFor(handler: *Handler, path: []const u8) ?[]const u8 {
        return (handler.session.files_new.get(path) orelse return null).source;
    }

    /// https://microsoft.github.io/language-server-protocol/specifications/specification-current/#textDocument_hover
    pub fn @"textDocument/hover"(
        handler: *Handler,
        arena: std.mem.Allocator,
        params: lsp.types.HoverParams,
    ) !?lsp.types.Hover {
        std.log.debug("Received 'textDocument/hover' request", .{});

        std.log.debug("on hover, uri is {s}", .{params.textDocument.uri});
        const path = try pathFromUri(params.textDocument.uri, arena);
        std.log.debug("on hover, path is {s}", .{path});

        const asdf: Swity.ParsedSource = handler.session.files_new.get(path) orelse {
            std.log.warn("Can't act on unknown Document: '{s}'", .{path});
            std.log.debug("known documents:", .{});
            var it = handler.session.files_new.iterator();
            while (it.next()) |kv| {
                std.log.debug("{s}", .{kv.key_ptr.*});
            }
            return null;
        };

        const source_index = lsp.offsets.positionToIndex(asdf.source, params.position, handler.offset_encoding);

        const nodes_under_cursor = try Swity.CST.nodesAt(arena, asdf.decls, source_index);
        std.log.debug("nodes under cursor: {any}", .{nodes_under_cursor});

        if (nodes_under_cursor.len == 0) {
            return null;
        } else {
            const last = nodes_under_cursor[nodes_under_cursor.len - 1];
            switch (last.tag) {
                else => return null,
                .identifier => {
                    const id = last.asString(asdf.source);

                    if (handler.session.known_types.get(id)) |declaration| {
                        const asdf_source = handler.sourceFor(declaration.position.span.uri);
                        std.log.debug("declaration span uri: {s}", .{declaration.position.span.uri});
                        std.log.debug("is asdfsource null: {any}", .{asdf_source == null});

                        return .{
                            .contents = .{
                                .MarkupContent = .{
                                    .kind = .markdown,
                                    .value = try std.fmt.allocPrint(arena, "```swt\n{s}\n```", .{
                                        declaration.position.asSourceCodeString(handler.sourceFor(declaration.position.span.uri) orelse return null),
                                    }),
                                },
                            },
                        };
                    } else if (handler.session.known_funcs.get(id)) |declaration| {
                        const decl_source = (handler.session.files_new.get(declaration.position.span.uri) orelse return null).source;
                        return .{
                            .contents = .{
                                .MarkupContent = .{
                                    .kind = .markdown,
                                    .value = try std.fmt.allocPrint(arena, "```swt\nfn {s}: {s} -> {s}\n```", .{
                                        declaration.position.children[0].asSourceCodeString(decl_source),
                                        declaration.position.children[1].asSourceCodeString(decl_source),
                                        declaration.position.children[2].asSourceCodeString(decl_source),
                                    }),
                                },
                            },
                        };
                        // } else return null;
                    } else {
                        var it = handler.session.known_types.iterator();
                        std.log.debug("known types:", .{});
                        while (it.next()) |kv| {
                            std.log.debug("name {s}", .{kv.key_ptr.*});
                        }
                        return null;
                    }
                },
            }
        }
    }

    /// https://microsoft.github.io/language-server-protocol/specifications/specification-current/#textDocument_definition
    pub fn @"textDocument/definition"(
        handler: *Handler,
        arena: std.mem.Allocator,
        params: lsp.types.DefinitionParams,
    ) !lsp.ResultType("textDocument/definition") {
        std.log.debug("Received 'textDocument/definition' request", .{});

        // TODO: uri starts with 'file:///c%3A/Users/...'

        const path = try pathFromUri(params.textDocument.uri, arena);
        std.log.debug("path at textDocument/defintion: {s}", .{path});

        const asdf: Swity.ParsedSource = handler.session.files_new.get(path) orelse {
            std.log.warn("Can't act on unknown Document: '{s}'", .{path});
            return null;
        };

        const source_index = lsp.offsets.positionToIndex(asdf.source, params.position, handler.offset_encoding);

        const nodes_under_cursor = try Swity.CST.nodesAt(arena, asdf.decls, source_index);

        if (nodes_under_cursor.len == 0) {
            return null;
        } else {
            const last = nodes_under_cursor[nodes_under_cursor.len - 1];
            switch (last.tag) {
                else => return null,
                .identifier => {
                    const id = last.asString(asdf.source);

                    const source_span = if (handler.session.known_types.get(id)) |declaration|
                        declaration.position.children[0].span
                    else if (handler.session.known_funcs.get(id)) |declaration|
                        declaration.position.children[0].span
                    else
                        null;

                    if (source_span) |span| {
                        const decl_source = handler.sourceFor(span.uri) orelse return null;
                        const start_pos = lsp.offsets.indexToPosition(decl_source, span.start, handler.offset_encoding);
                        const end_pos = lsp.offsets.indexToPosition(decl_source, span.start + span.len, handler.offset_encoding);
                        return .{
                            .Definition = .{
                                .Location = .{
                                    .uri = try uriFromPath(span.uri, arena),
                                    .range = .{
                                        .start = start_pos,
                                        .end = end_pos,
                                    },
                                },
                            },
                        };
                    } else return null;
                },
            }
        }
    }

    /// We received a response message from the client/editor.
    pub fn onResponse(
        _: *Handler,
        _: std.mem.Allocator,
        response: lsp.JsonRPCMessage.Response,
    ) void {
        // We didn't make any requests to the client/editor.
        std.log.warn("received unexpected response from client with id '{?}'!", .{response.id});
    }
};

// TODO: use https://github.com/zigtools/zls/blob/master/src/uri.zig

fn uriFromPath(path: []const u8, arena: std.mem.Allocator) ![]const u8 {
    const uri: std.Uri = try .parseAfterScheme("file", path);
    var res_buffer: std.ArrayList(u8) = .init(arena);
    try uri.format("", .{}, res_buffer.writer());
    return try res_buffer.toOwnedSlice();
}

fn pathFromUri(uri: []const u8, arena: std.mem.Allocator) ![]const u8 {
    const true_uri: std.Uri = try .parse(uri);
    assert(null == true_uri.fragment);
    assert(null == true_uri.host);
    assert(null == true_uri.password);
    assert(null == true_uri.port);
    assert(null == true_uri.query);
    assert(null == true_uri.user);
    assert(std.mem.eql(u8, "file", true_uri.scheme));
    const result = try true_uri.path.toRawMaybeAlloc(arena);
    // windows-specific hack: transform "/c:/..." into "C:/..."
    if (@import("builtin").target.os.tag == .windows) {
        assert(result[0] == '/');
        assert(result[2] == ':');
        const result2 = try arena.dupe(u8, result[1..]);
        result2[0] = std.ascii.toUpper(result2[0]);
        return result2;
    }
    return result;
}

test "path from uri" {
    if (@import("builtin").target.os.tag == .windows) {
        var arena: std.heap.ArenaAllocator = .init(std.testing.allocator);
        defer arena.deinit();

        const expected: []const u8 = "C:/Users/foo.swt";
        const actual: []const u8 = try pathFromUri("file:///c%3A/Users/foo.swt", arena.allocator());
        try std.testing.expectEqualStrings(expected, actual);
    }
}

test "uri parts" {
    const uri: std.Uri = try .parse("file:///C:/foo/file.swt");
    try std.testing.expectEqual(null, uri.fragment);
    try std.testing.expectEqual(null, uri.host);
    try std.testing.expectEqual(null, uri.password);
    try std.testing.expectEqual(null, uri.port);
    try std.testing.expectEqual(null, uri.query);
    try std.testing.expectEqual(null, uri.user);
    try std.testing.expectEqualStrings("file", uri.scheme);
}

test "resolve uri" {
    const base: std.Uri = try .parse("file:///C:/foo/file.swt");
    const relative: []const u8 = "../bar/baz.swt";
    const expected: std.Uri = try .parse("file:///C:/bar/baz.swt");
    var buf: [0x1000]u8 = undefined;
    var buf2: []u8 = &buf;
    const actual = try std.Uri.resolve_inplace(base, relative, &buf2);
    try std.testing.expectEqualDeep(expected, actual);
}

const std = @import("std");
const assert = std.debug.assert;
const lsp = @import("lsp");

const Swity = @import("Swity.zig");
