const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    const ktrc_dep = b.dependency("ktrc", .{});

    // ── Library tests ───────────────────────────────────────────

    const lib_mod = b.createModule(.{
        .root_source_file = b.path("src/root.zig"),
        .target = target,
        .optimize = optimize,
    });
    lib_mod.addImport("ktr_ir", ktrc_dep.module("ktr_ir"));

    const unit_tests = b.addTest(.{ .root_module = lib_mod });
    const run_tests = b.addRunArtifact(unit_tests);

    const test_step = b.step("test", "Run all ktrr tests");
    test_step.dependOn(&run_tests.step);

    // ── WASM module ─────────────────────────────────────────────

    const wasm_mod = b.createModule(.{
        .root_source_file = b.path("src/wasm.zig"),
        .target = b.resolveTargetQuery(.{
            .cpu_arch = .wasm32,
            .os_tag = .freestanding,
        }),
        .optimize = .ReleaseSmall,
        .strip = true,
        .single_threaded = true,
        .unwind_tables = .none,
        .error_tracing = false,
        .omit_frame_pointer = true,
    });
    wasm_mod.addImport("ktr_ir", ktrc_dep.module("ktr_ir"));

    const wasm = b.addExecutable(.{
        .name = "ktrr",
        .root_module = wasm_mod,
    });
    wasm.entry = .disabled;
    wasm.rdynamic = true;

    // ── wasm-opt post-processing (binaryen) ───────────────────

    const wasm_opt = b.addSystemCommand(&.{
        "wasm-opt",
        "-Oz",
        "--zero-filled-memory",
        "--enable-bulk-memory",
        "--enable-nontrapping-float-to-int",
        "--enable-sign-ext",
        "--enable-mutable-globals",
    });
    wasm_opt.addFileArg(wasm.getEmittedBin());
    wasm_opt.addArg("-o");
    const optimized_wasm = wasm_opt.addOutputFileArg("ktrr.wasm");

    const install_wasm = b.addInstallBinFile(optimized_wasm, "ktrr.wasm");
    const wasm_step = b.step("wasm", "Build ktrr WASM module");
    wasm_step.dependOn(&install_wasm.step);
}
