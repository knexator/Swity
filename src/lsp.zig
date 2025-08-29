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

pub const Handler = struct {
    allocator: std.mem.Allocator,
    files: std.StringHashMapUnmanaged([]u8),
    /// The LSP protocol specifies position inside a text document using a line and character pair.
    /// This field stores which encoding is used for the character value (UTF-8, UTF-16, UTF-32).
    ///
    /// https://microsoft.github.io/language-server-protocol/specifications/specification-current/#textDocuments
    offset_encoding: lsp.offsets.Encoding,

    fn init(allocator: std.mem.Allocator) Handler {
        return .{
            .allocator = allocator,
            .files = .{},
            // The default position encoding is UTF-16.
            // The agreed upon encoding between server client is actually decided during `initialize`.
            .offset_encoding = .@"utf-16",
        };
    }

    fn deinit(handler: *Handler) void {
        var file_it = handler.files.iterator();
        while (file_it.next()) |entry| {
            handler.allocator.free(entry.key_ptr.*);
            handler.allocator.free(entry.value_ptr.*);
        }

        handler.files.deinit(handler.allocator);

        handler.* = undefined;
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
                .name = "My first LSP",
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
        _: std.mem.Allocator,
        notification: lsp.types.DidOpenTextDocumentParams,
    ) !void {
        std.log.debug("Received 'textDocument/didOpen' notification", .{});

        const new_text = try self.allocator.dupe(u8, notification.textDocument.text);
        errdefer self.allocator.free(new_text);

        const gop = try self.files.getOrPut(self.allocator, notification.textDocument.uri);

        if (gop.found_existing) {
            std.log.warn("Document opened twice: '{s}'", .{notification.textDocument.uri});
            self.allocator.free(gop.value_ptr.*);
        } else {
            errdefer std.debug.assert(self.files.remove(notification.textDocument.uri));
            gop.key_ptr.* = try self.allocator.dupe(u8, notification.textDocument.uri);
        }

        gop.value_ptr.* = new_text;
    }

    /// https://microsoft.github.io/language-server-protocol/specifications/specification-current/#textDocument_didChange
    pub fn @"textDocument/didChange"(
        self: *Handler,
        _: std.mem.Allocator,
        notification: lsp.types.DidChangeTextDocumentParams,
    ) !void {
        std.log.debug("Received 'textDocument/didChange' notification", .{});

        const current_text = self.files.getPtr(notification.textDocument.uri) orelse {
            std.log.warn("Modifying non existent Document: '{s}'", .{notification.textDocument.uri});
            return;
        };

        var buffer: std.ArrayListUnmanaged(u8) = .empty;
        errdefer buffer.deinit(self.allocator);

        try buffer.appendSlice(self.allocator, current_text.*);

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
        self.allocator.free(current_text.*);
        current_text.* = new_text;
    }

    /// https://microsoft.github.io/language-server-protocol/specifications/specification-current/#textDocument_didClose
    pub fn @"textDocument/didClose"(
        self: *Handler,
        _: std.mem.Allocator,
        notification: lsp.types.DidCloseTextDocumentParams,
    ) !void {
        std.log.debug("Received 'textDocument/didClose' notification", .{});

        const entry = self.files.fetchRemove(notification.textDocument.uri) orelse {
            std.log.warn("Closing non existent Document: '{s}'", .{notification.textDocument.uri});
            return;
        };
        self.allocator.free(entry.key);
        self.allocator.free(entry.value);
    }

    /// https://microsoft.github.io/language-server-protocol/specifications/specification-current/#textDocument_hover
    ///
    /// This function can be omitted if you are not interested in this request. A `null` response will be automatically send back.
    pub fn @"textDocument/hover"(
        handler: *Handler,
        _: std.mem.Allocator,
        params: lsp.types.HoverParams,
    ) ?lsp.types.Hover {
        std.log.debug("Received 'textDocument/hover' request", .{});

        const source = handler.files.get(params.textDocument.uri) orelse {
            std.log.err("TODO: read file from fs", .{});
            return null;
        };

        const source_index = lsp.offsets.positionToIndex(source, params.position, handler.offset_encoding);
        std.log.debug("Hover position: line={d}, character={d}, index={d}", .{ params.position.line, params.position.character, source_index });

        return .{
            .contents = .{
                .MarkupContent = .{
                    .kind = .plaintext,
                    .value = "this is the hover text shown",
                },
            },
        };
    }

    /// https://microsoft.github.io/language-server-protocol/specifications/specification-current/#textDocument_definition
    pub fn @"textDocument/definition"(
        handler: *Handler,
        arena: std.mem.Allocator,
        params: lsp.types.DefinitionParams,
    ) !lsp.ResultType("textDocument/definition") {
        std.log.debug("Received 'textDocument/definition' request", .{});

        // TODO: uri starts with 'file:///c%3A/Users/...'

        const source = handler.files.get(params.textDocument.uri) orelse {
            std.log.err("TODO: read file from fs", .{});
            return null;
        };

        const source_index = lsp.offsets.positionToIndex(source, params.position, handler.offset_encoding);

        // TODO: persistent session
        var session: Swity = .init(arena);
        {
            var it = handler.files.iterator();
            while (it.next()) |kv| {
                session.addFileWithSource(kv.key_ptr.*, kv.value_ptr.*);
            }
            try session.addAllPendingTextRecursive();
        }

        std.log.debug("cursor is at {d}", .{source_index});
        for (session.files_new.get(params.textDocument.uri).?.?) |declaration| {
            std.log.debug("declaration range: {d}..{d}", .{
                declaration.span.start,
                declaration.span.start + declaration.span.len,
            });
            if (declaration.containsIndex(source_index)) {
                const start_pos = lsp.offsets.indexToPosition(source, declaration.span.start, handler.offset_encoding);
                const end_pos = lsp.offsets.indexToPosition(source, declaration.span.start + declaration.span.len, handler.offset_encoding);
                return .{
                    .Definition = .{
                        .Location = .{
                            .uri = params.textDocument.uri,
                            .range = .{
                                .start = start_pos,
                                .end = end_pos,
                            },
                        },
                    },
                };
            }
        }

        return .{
            .Definition = .{
                .Location = .{
                    .uri = params.textDocument.uri,
                    .range = .{
                        .start = .{ .line = 0, .character = 0 },
                        .end = .{ .line = 1, .character = 0 },
                    },
                },
            },
        };
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

const std = @import("std");
const assert = std.debug.assert;
const lsp = @import("lsp");

const Swity = @import("Swity.zig");
