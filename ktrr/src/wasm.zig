const std = @import("std");
const ktr_ir = @import("ktr_ir");
const eval_mod = @import("eval.zig");

const allocator = std.heap.wasm_allocator;

// ─── Global result buffers ──────────────────────────────────────────────────

var output_buf: ?[]u8 = null;
var error_buf: ?[]u8 = null;

fn freeOutput() void {
    if (output_buf) |buf| allocator.free(buf);
    output_buf = null;
}

fn freeError() void {
    if (error_buf) |buf| allocator.free(buf);
    error_buf = null;
}

// ─── JSON serialization ────────────────────────────────────────────────────

fn writeBindingsJson(bindings: []const eval_mod.Binding) error{OutOfMemory}![]u8 {
    var alloc_writer = std.io.Writer.Allocating.init(allocator);
    errdefer alloc_writer.deinit();

    var jw = std.json.Stringify{ .writer = &alloc_writer.writer };

    jw.beginArray() catch return error.OutOfMemory;

    for (bindings) |binding| {
        jw.beginObject() catch return error.OutOfMemory;

        jw.objectField("name") catch return error.OutOfMemory;
        jw.write(binding.name) catch return error.OutOfMemory;

        jw.objectField("type") catch return error.OutOfMemory;
        jw.write(@tagName(binding.ty)) catch return error.OutOfMemory;

        jw.objectField("value") catch return error.OutOfMemory;
        writeRuntimeValueJson(&jw, binding.value) catch return error.OutOfMemory;

        if (binding.ty == .length) {
            jw.objectField("unit") catch return error.OutOfMemory;
            jw.write("mm") catch return error.OutOfMemory;
        }

        jw.objectField("isInput") catch return error.OutOfMemory;
        jw.write(binding.is_input) catch return error.OutOfMemory;

        jw.endObject() catch return error.OutOfMemory;
    }

    jw.endArray() catch return error.OutOfMemory;

    return alloc_writer.toOwnedSlice() catch return error.OutOfMemory;
}

fn writePointJson(jw: *std.json.Stringify, pt: [2]f64) std.json.Stringify.Error!void {
    try jw.beginObject();
    try jw.objectField("x");
    try writeJsonNumber(jw, pt[0]);
    try jw.objectField("y");
    try writeJsonNumber(jw, pt[1]);
    try jw.endObject();
}

fn writeRuntimeValueJson(jw: *std.json.Stringify, value: eval_mod.RuntimeValue) std.json.Stringify.Error!void {
    switch (value) {
        .scalar => |v| try writeJsonNumber(jw, v),
        .point => |p| try writePointJson(jw, p),
        .bezier => |pts| {
            try jw.beginObject();
            const labels = [_][]const u8{ "p1", "p2", "p3", "p4" };
            for (pts, labels) |pt, label| {
                try jw.objectField(label);
                try writePointJson(jw, pt);
            }
            try jw.endObject();
        },
        .line => |pts| {
            try jw.beginObject();
            const labels = [_][]const u8{ "start", "end" };
            for (pts, labels) |pt, label| {
                try jw.objectField(label);
                try writePointJson(jw, pt);
            }
            try jw.endObject();
        },
        .piece => |p| {
            try jw.beginObject();
            for (p.members) |member| {
                try jw.objectField(member.name);
                try writeRuntimeValueJson(jw, member.value);
            }
            try jw.endObject();
        },
    }
}

/// Write a f64 as a JSON number. Integer-valued floats are emitted without
/// a decimal point (e.g. `100` not `100.0` or `1e2`).
fn writeJsonNumber(jw: *std.json.Stringify, value: f64) std.json.Stringify.Error!void {
    try ktr_ir.formatF64(jw, value);
}

// ─── Override storage ───────────────────────────────────────────────────────

var override_list = std.ArrayList(eval_mod.InputOverride).empty;

// ─── Exported WASM API ──────────────────────────────────────────────────────

/// Allocate `len` bytes of WASM memory. Returns a pointer for JS to write into.
export fn alloc(len: usize) usize {
    const slice = allocator.alloc(u8, len) catch return 0;
    return @intFromPtr(slice.ptr);
}

/// Free a previously allocated region.
export fn dealloc(ptr: usize, len: usize) void {
    if (ptr == 0) return;
    const slice: [*]u8 = @ptrFromInt(ptr);
    allocator.free(slice[0..len]);
}

/// Set an input override by name. Called from JS before eval_ir.
/// The name is a WASM memory pointer+length. The value is already in mm.
export fn set_override(name_ptr: usize, name_len: usize, value: f64) void {
    if (name_ptr == 0 or name_len == 0) return;
    const raw: [*]const u8 = @ptrFromInt(name_ptr);
    const name_slice = raw[0..name_len];

    // Check if override already exists and update it.
    for (override_list.items) |*ov| {
        if (std.mem.eql(u8, ov.name, name_slice)) {
            ov.value = value;
            return;
        }
    }

    // New override: dupe the name.
    const name = allocator.dupe(u8, name_slice) catch return;
    override_list.append(allocator, .{ .name = name, .value = value }) catch {
        allocator.free(name);
    };
}

/// Clear all input overrides. Called from JS when source is recompiled.
export fn clear_overrides() void {
    for (override_list.items) |ov| {
        allocator.free(ov.name);
    }
    override_list.clearRetainingCapacity();
}

/// Evaluate `.ktrir` text and return JSON results.
///
/// Uses overrides previously set via set_override / clear_overrides.
///
/// Returns the output length on success (>= 0), or a negative error code:
///   -1  out of memory / internal error
///   -2  invalid IR format (check get_error_ptr / get_error_len)
///   -3  evaluation error  (check get_error_ptr / get_error_len)
export fn eval_ir(input_ptr: usize, input_len: usize) i32 {
    freeOutput();
    freeError();

    if (input_ptr == 0) return -1;
    const raw: [*]const u8 = @ptrFromInt(input_ptr);
    const source = raw[0..input_len];

    // Parse IR.
    var ir_data = ktr_ir.parse(allocator, source) catch {
        const msg = "invalid .ktrir input";
        error_buf = allocator.dupe(u8, msg) catch null;
        return -2;
    };
    defer ir_data.deinit();

    // Evaluate.
    var result = eval_mod.eval(allocator, ir_data, override_list.items) catch |err| {
        const msg: []const u8 = switch (err) {
            error.UndefinedReference => "undefined reference",
            error.DivisionByZero => "division by zero",
            error.UnsupportedOperation => "unsupported operation",
            error.OutOfMemory => return -1,
        };
        error_buf = allocator.dupe(u8, msg) catch null;
        return -3;
    };
    defer result.deinit();

    // Serialize to JSON.
    output_buf = writeBindingsJson(result.bindings) catch return -1;
    return @intCast(output_buf.?.len);
}

/// Pointer to the last successful output buffer.
export fn get_output_ptr() usize {
    if (output_buf) |buf| return @intFromPtr(buf.ptr);
    return 0;
}

/// Length of the last successful output buffer.
export fn get_output_len() usize {
    if (output_buf) |buf| return buf.len;
    return 0;
}

/// Pointer to the last error message buffer.
export fn get_error_ptr() usize {
    if (error_buf) |buf| return @intFromPtr(buf.ptr);
    return 0;
}

/// Length of the last error message buffer.
export fn get_error_len() usize {
    if (error_buf) |buf| return buf.len;
    return 0;
}
