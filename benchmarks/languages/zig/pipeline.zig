// The fused batch of ../../feature-pipeline (Rust mode 1), in Zig: a boxed
// ticket key, one vector at its final capacity, the fused transform and a
// checksum. ReleaseSafe checks the additions and indexing.
const std = @import("std");

fn scrub(x: i64) i64 {
    return (x & 65535) ^ (x & 255);
}

fn tag(x: i64) i64 {
    return x ^ 23130;
}

fn checksum(values: []const i64) i64 {
    var sum: i64 = 0;
    var i: usize = 0;
    while (i < values.len) : (i += 1) sum += values[i];
    return sum;
}

fn batch(gpa: std.mem.Allocator, n: usize) !i64 {
    const ticket = try gpa.create(i64);
    defer gpa.destroy(ticket);
    ticket.* = 23130;
    const values = try gpa.alloc(i64, n);
    defer gpa.free(values);
    for (values, 0..) |*value, i| value.* = @as(i64, @intCast(i)) & 65535;
    for (values) |*value| value.* = tag(scrub(value.*));
    return checksum(values) + ticket.*;
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
    const rounds = config[1];
    if (n < 1 or n > 8000000 or rounds < 0 or rounds > 32 or config[2] != 1) return 2;
    var result: i64 = 0;
    var round: i64 = 0;
    while (round < rounds) : (round += 1) result += try batch(init.gpa, @intCast(n));
    var buffer: [32]u8 = undefined;
    const text = try std.fmt.bufPrint(&buffer, "{d}\n", .{result});
    try std.Io.File.stdout().writeStreamingAll(init.io, text);
    return 0;
}
