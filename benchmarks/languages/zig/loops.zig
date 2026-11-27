// The three kernels of ../../checked-loops, in Zig. ReleaseSafe checks every
// +, - and * for overflow and every index against its slice (Kush
// semantics); ReleaseFast checks neither.
const std = @import("std");

noinline fn sum(values: []const i64) i64 {
    var acc: i64 = 0;
    var i: usize = 0;
    while (i < values.len) : (i += 1) acc += values[i];
    return acc;
}

noinline fn dot(left: []const i64, right: []const i64) i64 {
    var acc: i64 = 0;
    var i: usize = 0;
    while (i < left.len) : (i += 1) acc += left[i] * right[i];
    return acc;
}

noinline fn scale(source: []const i64, target: []i64, factor: i64) void {
    var i: usize = 0;
    while (i < source.len) : (i += 1) target[i] = source[i] * factor - 7;
}

fn fill(gpa: std.mem.Allocator, n: i64, salt: i64) ![]i64 {
    const values = try gpa.alloc(i64, @intCast(n));
    var i: i64 = 0;
    while (i < n) : (i += 1) values[@intCast(i)] = ((i * 7919 + salt) & 4095) - 2048;
    return values;
}

pub fn main(init: std.process.Init) !u8 {
    var it = init.minimal.args.iterate();
    _ = it.skip();
    var config: [3]i64 = undefined;
    var count: usize = 0;
    while (it.next()) |arg| : (count += 1) {
        if (count == 3) return 2;
        config[count] = std.fmt.parseInt(i64, arg, 10) catch return 2;
    }
    if (count != 3) return 2;
    const n = config[0];
    const repetitions = config[1];
    const kernel = config[2];
    if (n < 1 or n > 8000000 or repetitions < 0 or repetitions > 100000000 or kernel < 0 or kernel > 2) return 2;
    const gpa = init.gpa;
    const left = try fill(gpa, n, 17);
    defer gpa.free(left);
    const right = try fill(gpa, n, 4001);
    defer gpa.free(right);
    const scratch = try fill(gpa, n, 0);
    defer gpa.free(scratch);
    var result: i64 = 0;
    var round: i64 = 0;
    while (round < repetitions) : (round += 1) {
        const step = switch (kernel) {
            0 => sum(left),
            1 => dot(left, right),
            else => blk: {
                scale(left, scratch, (round & 3) + 2);
                break :blk sum(scratch);
            },
        };
        result = (result ^ step) + (round & 1);
    }
    var buffer: [32]u8 = undefined;
    const text = try std.fmt.bufPrint(&buffer, "{d}\n", .{result});
    try std.Io.File.stdout().writeStreamingAll(init.io, text);
    return 0;
}
