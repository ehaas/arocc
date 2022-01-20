const std = @import("std");
const Builder = std.build.Builder;

fn addFuzzStep(b: *Builder, target: std.zig.CrossTarget) !void {
    const fuzz_lib = b.addStaticLibrary("fuzz-lib", "test/fuzz/fuzz_lib.zig");
    fuzz_lib.addPackagePath("aro", "src/lib.zig");
    fuzz_lib.setTarget(target);
    fuzz_lib.setBuildMode(.Debug);
    fuzz_lib.want_lto = true;
    fuzz_lib.bundle_compiler_rt = true;

    const fuzz_lib_step = b.step("fuzz", "Build fuzz library");
    fuzz_lib_step.dependOn(&fuzz_lib.step);
}

pub fn build(b: *Builder) !void {
    // Standard target options allows the person running `zig build` to choose
    // what target to build for. Here we do not override the defaults, which
    // means any target is allowed, and the default is native. Other options
    // for restricting supported target set are available.
    const target = b.standardTargetOptions(.{});

    // Standard release options allow the person running `zig build` to select
    // between Debug, ReleaseSafe, ReleaseFast, and ReleaseSmall.
    const mode = b.standardReleaseOptions();

    const zig_pkg = std.build.Pkg{
        .name = "zig",
        .path = .{ .path = "deps/zig/lib.zig" },
    };

    const exe = b.addExecutable("arocc", "src/main.zig");
    exe.setTarget(target);
    exe.setBuildMode(mode);
    exe.addPackage(zig_pkg);
    exe.install();

    const run_cmd = exe.run();
    run_cmd.step.dependOn(b.getInstallStep());
    if (b.args) |args| {
        run_cmd.addArgs(args);
    }

    const run_step = b.step("run", "Run the app");
    run_step.dependOn(&run_cmd.step);

    const tests_step = b.step("test", "Run all tests");
    tests_step.dependOn(&exe.step);

    var unit_tests = b.addTest("src/main.zig");
    unit_tests.addPackage(zig_pkg);
    tests_step.dependOn(&unit_tests.step);

    const integration_tests = b.addExecutable("arocc", "test/runner.zig");
    integration_tests.addPackage(.{
        .name = "aro",
        .path = .{ .path = "src/lib.zig" },
        .dependencies = &.{zig_pkg},
    });

    const integration_test_runner = integration_tests.run();
    integration_test_runner.addArg(b.pathFromRoot("test/cases"));
    integration_test_runner.addArg(b.zig_exe);
    tests_step.dependOn(&integration_test_runner.step);

    try addFuzzStep(b, target);
}
