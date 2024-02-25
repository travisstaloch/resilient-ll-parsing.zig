const std = @import("std");
const assert = std.debug.assert;

pub fn predLength(pred: *const fn (u8) bool, text: []const u8) ?u32 {
    var i: u32 = 0;
    while (i < text.len and pred(text[i])) : (i += 1) {}
    return if (i > 0) i else null;
}

pub fn name_char(c: u8) bool {
    return std.ascii.isAlphanumeric(c) or c == '_';
}
