const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    // ── Public module (consumed by ktrr and other dependents) ──

    _ = b.addModule("ktr_ir", .{
        .root_source_file = b.path("src/ktr_ir.zig"),
    });

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
        .strip = true, // strip debug info & DWARF
        .single_threaded = true, // no threading overhead
        .unwind_tables = .none, // no unwind tables needed in freestanding wasm
        .error_tracing = false, // no error return traces
        .omit_frame_pointer = true, // smaller call frames
    });

    const wasm = b.addExecutable(.{
        .name = "ktrc",
        .root_module = wasm_mod,
    });
    wasm.entry = .disabled;
    wasm.rdynamic = true;

    // ── wasm-opt post-processing (binaryen) ───────────────────
    // Runs `wasm-opt -Oz` for WASM-specific size optimisations
    // that Zig's codegen doesn't perform (~9% smaller output).

    const wasm_opt = b.addSystemCommand(&.{
        "wasm-opt",
        "-Oz", // aggressive size optimisation
        "--zero-filled-memory", // memory is zero-initialized
        "--enable-bulk-memory", // Zig emits memory.copy/fill
        "--enable-nontrapping-float-to-int", // Zig emits trunc_sat
        "--enable-sign-ext", // Zig emits sign-extension ops
        "--enable-mutable-globals", // Zig emits mutable globals
    });
    wasm_opt.addFileArg(wasm.getEmittedBin());
    wasm_opt.addArg("-o");
    const optimized_wasm = wasm_opt.addOutputFileArg("ktrc.wasm");

    const install_wasm = b.addInstallBinFile(optimized_wasm, "ktrc.wasm");
    const wasm_step = b.step("wasm", "Build ktrc WASM module");
    wasm_step.dependOn(&install_wasm.step);
}
