const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    // ── Library tests ───────────────────────────────────────────

    const lib_mod = b.createModule(.{
        .root_source_file = b.path("src/root.zig"),
        .target = target,
        .optimize = optimize,
    });
    const unit_tests = b.addTest(.{ .root_module = lib_mod });
    const run_tests = b.addRunArtifact(unit_tests);

    const test_step = b.step("test", "Run all ktrc tests");
    test_step.dependOn(&run_tests.step);

    // ── Executable ──────────────────────────────────────────────

    const exe_mod = b.createModule(.{
        .root_source_file = b.path("src/main.zig"),
        .target = target,
        .optimize = optimize,
    });
    const exe = b.addExecutable(.{ .name = "ktrc", .root_module = exe_mod });
    b.installArtifact(exe);

    // `zig build run -- compile program.ktr`
    const run_cmd = b.addRunArtifact(exe);
    run_cmd.step.dependOn(b.getInstallStep());
    if (b.args) |args| {
        run_cmd.addArgs(args);
    }

    const run_step = b.step("run", "Run ktrc");
    run_step.dependOn(&run_cmd.step);

    // ── WASM module ─────────────────────────────────────────────

    const wasm_mod = b.createModule(.{
        .root_source_file = b.path("src/wasm.zig"),
        .target = b.resolveTargetQuery(.{
            .cpu_arch = .wasm32,
            .os_tag = .freestanding,
        }),
        .optimize = .ReleaseSmall,
    });

    const wasm = b.addExecutable(.{
        .name = "ktrc",
        .root_module = wasm_mod,
    });
    wasm.entry = .disabled;
    wasm.rdynamic = true;

    const install_wasm = b.addInstallArtifact(wasm, .{});
    const wasm_step = b.step("wasm", "Build ktrc WASM module");
    wasm_step.dependOn(&install_wasm.step);
}
