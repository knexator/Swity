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

    var got_args = false;

    var session: Swity = .init(gpa);
    defer session.deinit();
    while (args.next()) |arg| {
        got_args = true;
        const source_code = try std.fs.cwd().readFileAlloc(gpa, arg, std.math.maxInt(usize));
        defer gpa.free(source_code);
        session.addText(source_code);
    }

    if (got_args) {
        const result = session.executeMain();
        try stdout.print("{any}\n", .{result});
    } else {
        try stdout.print("Usage: swity [files]", .{});
    }

    try bw.flush();
}

comptime {
    std.testing.refAllDecls(Swity);
}

const std = @import("std");
const assert = std.debug.assert;
const Swity = @import("Swity.zig");
