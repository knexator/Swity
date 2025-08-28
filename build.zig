const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    const lsp = b.dependency("lsp_kit", .{}).module("lsp");

    const exe_mod = b.createModule(.{
        .root_source_file = b.path("src/main.zig"),
        .target = target,
        .optimize = optimize,
        .imports = &.{
            .{ .name = "lsp", .module = lsp },
        },
    });

    const exe = b.addExecutable(.{
        .name = "swity",
        .root_module = exe_mod,
    });

    b.installArtifact(exe);

    {
        const run_cmd = b.addRunArtifact(exe);
        run_cmd.step.dependOn(b.getInstallStep());
        if (b.args) |args| {
            run_cmd.addArgs(args);
        }
        const run_step = b.step("run", "Run the app");
        run_step.dependOn(&run_cmd.step);
    }

    {
        const exe_unit_tests = b.addTest(.{
            .root_module = exe_mod,
        });
        const run_exe_unit_tests = b.addRunArtifact(exe_unit_tests);
        const test_step = b.step("test", "Run unit tests");
        test_step.dependOn(&run_exe_unit_tests.step);
    }

    {
        const run_cmd = b.addRunArtifact(exe);
        run_cmd.step.dependOn(b.getInstallStep());
        run_cmd.addArg("run");
        run_cmd.addFileArg(b.path("examples/advent_of_code.swt"));
        run_cmd.expectStdOutEqual(
            \\("0" ("9" ("6" ("4" ("7" ("5" ("3" "nil")))))))
            \\
        );
        const run_step = b.step("e2e", "Run end-to-end tests");
        run_step.dependOn(&run_cmd.step);
    }
}
