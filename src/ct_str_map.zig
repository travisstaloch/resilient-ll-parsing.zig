const std = @import("std");

/// this is an adaptation of std.ComptimeStringMap() which does integer
/// comparisons rather than string comparison.  entries are stored in an
/// `entries_by_length` array whose length is equal to the distinct count of
/// entry key lengths.  because of this, this data structure may not be well suited for sets
/// of strings with widely different lengths or those with very long lengths.
/// they may require excessive memory and lose cache locality.
/// for instance, consider a set with 100 strings of length 8 and one string
/// with length 40.  this would result an in `entries_by_len` array
/// of length 2 and and with integer bit width 40*8 = 320.
pub fn ComptimeStringMap(comptime T: type, comptime entries: anytype) type {
    comptime {
        var longest_len: usize = 0;
        for (entries) |e| {
            longest_len = @max(longest_len, e[0].len);
        }

        var lengths_bitset: std.meta.Int(.unsigned, longest_len + 1) = 0;
        var distinct_lengths: []const usize = &.{};
        for (entries) |e| {
            const bit = 1 << e[0].len;
            if (lengths_bitset & bit == 0) {
                lengths_bitset |= bit;
                distinct_lengths = distinct_lengths ++ [1]usize{e[0].len};
            }
        }

        const I = std.meta.Int(.unsigned, longest_len * 8);
        std.debug.assert(distinct_lengths.len == @popCount(lengths_bitset));
        const Entry = struct { I, T };

        var entries_by_len = [1][]const Entry{&.{}} ** (distinct_lengths.len + 1);
        for (entries) |e| {
            const k = e[0];
            const v = e[1];
            const J = std.meta.Int(.unsigned, k.len * 8);
            const index = @popCount(lengths_bitset & (1 << k.len) - 1);
            entries_by_len[index] = entries_by_len[index] ++
                [1]Entry{.{ std.mem.readInt(J, k[0..k.len], .little), v }};
        }
        var lengths = distinct_lengths[0..distinct_lengths.len].*;
        std.mem.sort(usize, &lengths, {}, std.sort.desc(usize));
        for (lengths) |l| {
            const index = @popCount(lengths_bitset & (1 << l) - 1);
            var es = entries_by_len[index];
            var arr = es[0..es.len].*;
            std.mem.sort(Entry, &arr, {}, struct {
                fn sort(_: void, a: Entry, b: Entry) bool {
                    return a[0] < b[0];
                }
            }.sort);
            // @compileLog(arr);
            entries_by_len[index] = &arr;
        }

        return struct {
            pub const kvs = entries;
            /// returns any value which exactly matches 'key' or null.
            pub fn get(key: []const u8) ?T {
                // std.debug.print("get({s})\n", .{key});
                inline for (lengths) |l| {
                    if (key.len == l) {
                        const J = std.meta.Int(.unsigned, l * 8);
                        const j = std.mem.readInt(J, key[0..l], .little);
                        const index = @popCount(lengths_bitset & (1 << l) - 1);
                        for (entries_by_len[index]) |e| {
                            const i: J = @truncate(e[0]);
                            if (j == i) return e[1];
                        }
                    }
                }
                return null;
            }

            pub const KV = struct { key: []const u8, value: T };
            /// returns the longest matching key, value pair found at the start
            /// of 's' or null when no match is found.
            pub fn getPartial(s: []const u8) ?KV {
                // var count: usize = 0;
                // std.debug.print("getPartial('{s}')\n", .{s[0..@min(s.len, 10)]});
                // defer std.debug.print("count={}\n", .{count});
                inline for (lengths) |l| {
                    if (s.len >= l) {
                        const J = std.meta.Int(.unsigned, l * 8);
                        const j = std.mem.readInt(J, s[0..l], .little);
                        // count += 1;
                        const index = @popCount(lengths_bitset & (1 << l) - 1);
                        // std.debug.print("s='{s}' l={} {any}\n", .{ s[0..l], l, entries_by_len[index] });
                        for (entries_by_len[index]) |e| {
                            const i: J = @truncate(e[0]);
                            // count += 1;
                            if (j == i) {
                                return .{ .key = std.mem.asBytes(&e[0])[0..l], .value = e[1] };
                            }
                        }
                    }
                }
                return null;
            }
        };
    }
}

test {
    const map = ComptimeStringMap(usize, .{
        .{ "one", 1 },
        .{ "two", 2 },
        .{ "three", 3 },
        .{ "four", 4 },
        .{ "five", 5 },
        .{ "six", 6 },
        .{ "seven", 7 },
        .{ "eight", 8 },
        .{ "nine", 9 },
    });

    try std.testing.expectEqual(@as(?usize, 1), map.get("one"));
    try std.testing.expectEqual(@as(?usize, null), map.get("o"));
    try std.testing.expectEqual(@as(?usize, null), map.get("onexxx"));
    try std.testing.expectEqual(@as(?usize, 9), map.get("nine"));
    try std.testing.expectEqual(@as(?usize, null), map.get("n"));
    try std.testing.expectEqual(@as(?usize, null), map.get("ninexxx"));
    try std.testing.expectEqual(@as(?usize, null), map.get("xxx"));

    try std.testing.expectEqual(@as(usize, 1), map.getPartial("one").?.value);
    try std.testing.expectEqual(@as(usize, 1), map.getPartial("onexxx").?.value);
    try std.testing.expectEqual(@as(?map.KV, null), map.getPartial("o"));
    try std.testing.expectEqual(@as(usize, 9), map.getPartial("nine").?.value);
    try std.testing.expectEqual(@as(usize, 9), map.getPartial("ninexxx").?.value);
    try std.testing.expectEqual(@as(?map.KV, null), map.getPartial("n"));
    try std.testing.expectEqual(@as(?map.KV, null), map.getPartial("xxx"));
}
