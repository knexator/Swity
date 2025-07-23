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

    var session: Swity = .init(gpa);
    defer session.deinit();
    session.addText(
        \\ data Natural {
        \\      "zero",
        \\      ("succ" Natural),
        \\ }
        \\
        // \\ fn sum: (Natural Natural) -> Natural {
        // \\      ("zero" b) -> b;
        // \\      (("succ" a) b) -> sum: (a ("succ" b));
        // \\ }
    );

    // const stdout_file = std.io.getStdOut().writer();
    // var bw = std.io.bufferedWriter(stdout_file);
    // const stdout = bw.writer();

    // try bw.flush();
}

test "simple test" {
    var list = std.ArrayList(i32).init(std.testing.allocator);
    defer list.deinit(); // Try commenting this out and see if zig detects the memory leak!
    try list.append(42);
    try std.testing.expectEqual(@as(i32, 42), list.pop());
}

comptime {
    std.testing.refAllDecls(Swity);
}

const std = @import("std");
const assert = std.debug.assert;
const Swity = @import("Swity.zig");
