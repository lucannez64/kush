// The kernels of ../kush/main.kush in Zig, built ReleaseSafe. The fourth
// argument picks the form: 0 checks every index and every operation, 1 skips
// exactly what Kush proves (unchecked many-pointer reads, wrapping window
// arithmetic). The accumulators stay checked in both forms, as in Kush.
const std = @import("std");

noinline fn sum(comptime trusted: bool, values: []const i64) i64 {
    var acc: i64 = 0;
    var i: usize = 0;
    while (i < values.len) : (i += 1) acc += if (trusted) values.ptr[i] else values[i];
    return acc;
}

noinline fn stencil(comptime trusted: bool, data: []const u8) i64 {
    var acc: i64 = 0;
    var i: usize = 1;
    while (i < data.len - 1) : (i += 1) {
        const window: i64 = if (trusted)
            @as(i64, data.ptr[i -% 1]) +% 2 *% @as(i64, data.ptr[i]) +% @as(i64, data.ptr[i +% 1])
        else
            @as(i64, data[i - 1]) + 2 * @as(i64, data[i]) + @as(i64, data[i + 1]);
        acc += window;
    }
    return acc;
}

noinline fn crc32(comptime trusted: bool, table: []const u32, crc: u32, data: []const u8) u32 {
    var c = crc ^ 0xFFFF_FFFF;
    var i: usize = 0;
    while (i < data.len) : (i += 1) {
        const byte: u32 = if (trusted) data.ptr[i] else data[i];
        const index = (c ^ byte) & 255;
        c = (if (trusted) table.ptr[index] else table[index]) ^ (c >> 8);
    }
    return c ^ 0xFFFF_FFFF;
}

noinline fn lookup(comptime trusted: bool, table: []const i64, data: []const u8) i64 {
    var acc: i64 = 0;
    var i: usize = 0;
    while (i < data.len) : (i += 1) {
        const at: usize = if (trusted) data.ptr[i] else data[i];
        acc += if (trusted) table.ptr[at] else table[at];
    }
    return acc;
}

noinline fn follow(comptime trusted: bool, values: []const i64) i64 {
    var acc: i64 = 0;
    var i: usize = 0;
    var j: usize = 0;
    while (i < values.len) : (i += 1) {
        acc += if (trusted) values.ptr[j] else values[j];
        if ((if (trusted) values.ptr[i] else values[i]) > 0) j += 1;
    }
    return acc;
}

fn run(comptime trusted: bool, gpa: std.mem.Allocator, n: i64, repetitions: i64, kernel: i64) !i64 {
    const values = try gpa.alloc(i64, @intCast(n));
    defer gpa.free(values);
    const data = try gpa.alloc(u8, @intCast(n));
    defer gpa.free(data);
    var i: i64 = 0;
    while (i < n) : (i += 1) {
        values[@intCast(i)] = ((i * 7919 + 17) & 4095) - 2048;
        data[@intCast(i)] = @intCast((i * 7 + 3) & 255);
    }
    const table = try gpa.alloc(u32, 256);
    defer gpa.free(table);
    for (table, 0..) |*entry, k| {
        var c: u32 = @intCast(k);
        var bit: usize = 0;
        while (bit < 8) : (bit += 1) c = if (c & 1 == 1) 0xEDB8_8320 ^ (c >> 1) else c >> 1;
        entry.* = c;
    }
    // At least 256 entries, checked once here as Kush's field type checks it.
    const codec = try gpa.alloc(i64, 256);
    defer gpa.free(codec);
    for (codec, 0..) |*entry, k| entry.* = ((@as(i64, @intCast(k)) * 40503 + 7) & 1023) - 512;
    if (codec.len < 256) return error.ShortTable;
    var result: i64 = 0;
    var round: i64 = 0;
    while (round < repetitions) : (round += 1) {
        const step: i64 = switch (kernel) {
            0 => sum(trusted, values),
            1 => stencil(trusted, data),
            3 => lookup(trusted, codec, data),
            4 => follow(trusted, values),
            else => crc32(trusted, table, @truncate(@as(u64, @bitCast(round))), data),
        };
        result = (result ^ step) + (round & 1);
    }
    return result;
}

pub fn main(init: std.process.Init) !u8 {
    var it = init.minimal.args.iterate();
    _ = it.skip();
    var config: [4]i64 = undefined;
    var count: usize = 0;
    while (it.next()) |arg| : (count += 1) {
        if (count == 4) return 2;
        config[count] = std.fmt.parseInt(i64, arg, 10) catch return 2;
    }
    if (count != 4) return 2;
    const n = config[0];
    const repetitions = config[1];
    const kernel = config[2];
    const trusted = config[3];
    if (n < 3 or n > 8000000 or repetitions < 0 or repetitions > 100000000 or kernel < 0 or kernel > 4 or trusted < 0 or trusted > 1) return 2;
    const result = if (trusted == 1)
        try run(true, init.gpa, n, repetitions, kernel)
    else
        try run(false, init.gpa, n, repetitions, kernel);
    var buffer: [32]u8 = undefined;
    const text = try std.fmt.bufPrint(&buffer, "{d}\n", .{result});
    try std.Io.File.stdout().writeStreamingAll(init.io, text);
    return 0;
}
