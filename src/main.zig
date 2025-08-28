pub fn main() !void {
    var debug_allocator: std.heap.DebugAllocator(.{}) = .init;
    const gpa, const is_debug = gpa: {
        if (@import("builtin").os.tag == .wasi) break :gpa .{ std.heap.wasm_allocator, false };
        break :gpa switch (@import("builtin").mode) {
            .Debug, .ReleaseSafe => .{ debug_allocator.allocator(), true },
            .ReleaseFast, .ReleaseSmall => .{ std.heap.smp_allocator, false },
        };
    };
    defer if (is_debug) {
        assert(debug_allocator.deinit() == .ok);
    };

    const stdout_file = std.io.getStdOut().writer();
    var bw = std.io.bufferedWriter(stdout_file);
    const stdout = bw.writer();

    var args = try std.process.argsWithAllocator(gpa);
    defer args.deinit();
    assert(args.skip());

    const mode = args.next() orelse "help";

    if (std.mem.eql(u8, mode, "lsp")) {
        try @import("lsp.zig").run(gpa);
    } else if (std.mem.eql(u8, mode, "run")) {
        var session: Swity = .init(gpa);
        defer session.deinit();
        while (args.next()) |arg| {
            const path = try std.fs.cwd().realpathAlloc(gpa, arg);
            defer gpa.free(path);
            session.addIncludeFile(path);
        }
        const result = try session.executeMain();
        try stdout.print("{any}\n", .{result});
    } else {
        try stdout.print("Usage:\n\tswity run [files]\n\tswity lsp", .{});
    }

    try bw.flush();
}

comptime {
    std.testing.refAllDecls(Swity);
}

const std = @import("std");
const assert = std.debug.assert;
const Swity = @import("Swity.zig");
