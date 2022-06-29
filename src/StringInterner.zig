//! Adapted from code in https://github.com/ziglang/zig/blob/76546b3f8e19b11f0c88259b1b3e5fd14cfbde31/src/AstGen.zig
//! Uses null-termination to delimit stored strings, so interned strings may not have embedded null characters

const std = @import("std");
const mem = std.mem;
const Allocator = mem.Allocator;

const StringInterner = @This();

pub const Id = enum(u32) {
    _,
};

const StringToIndexMap = std.HashMapUnmanaged(Id, void, StringIndexContext, std.hash_map.default_max_load_percentage);

fn stringAt(bytes: [*]const u8, id: Id) []const u8 {
    return mem.sliceTo(@ptrCast([*:0]const u8, bytes) + @enumToInt(id), 0);
}

const StringIndexContext = struct {
    bytes: [*]const u8,

    pub fn eql(self: @This(), a: Id, b: Id) bool {
        _ = self;
        return a == b;
    }

    pub fn hash(self: @This(), x: Id) u64 {
        const x_slice = stringAt(self.bytes, x);
        return std.hash_map.hashString(x_slice);
    }
};

const StringIndexAdapter = struct {
    bytes: [*]const u8,

    pub fn eql(self: @This(), a_slice: []const u8, b: Id) bool {
        const b_slice = stringAt(self.bytes, b);
        return mem.eql(u8, a_slice, b_slice);
    }

    pub fn hash(self: @This(), adapted_key: []const u8) u64 {
        _ = self;
        return std.hash_map.hashString(adapted_key);
    }
};

string_bytes: std.ArrayListUnmanaged(u8) = .{},
string_table: StringToIndexMap = .{},

pub fn intern(self: *StringInterner, allocator: Allocator, str: []const u8) !Id {
    std.debug.assert(mem.indexOfScalar(u8, str, 0) == null);
    const str_index = @intCast(u32, self.string_bytes.items.len);
    try self.string_bytes.appendSlice(allocator, str);
    const key = self.string_bytes.items[str_index..];
    const gop = try self.string_table.getOrPutContextAdapted(allocator, @as([]const u8, key), StringIndexAdapter{
        .bytes = self.string_bytes.items.ptr,
    }, StringIndexContext{
        .bytes = self.string_bytes.items.ptr,
    });
    if (gop.found_existing) {
        self.string_bytes.shrinkRetainingCapacity(str_index);
        return gop.key_ptr.*;
    } else {
        gop.key_ptr.* = @intToEnum(Id, str_index);
        try self.string_bytes.append(allocator, 0);
        return @intToEnum(Id, str_index);
    }
}

pub fn getString(self: *const StringInterner, id: Id) []const u8 {
    return stringAt(self.string_bytes.items.ptr, id);
}

pub fn deinit(self: *StringInterner, allocator: Allocator) void {
    self.string_bytes.deinit(allocator);
    self.string_table.deinit(allocator);
}

test "StringInterner" {
    const S = struct {
        fn testInterner(allocator: Allocator) !void {
            var si = StringInterner{};
            defer si.deinit(allocator);

            const hello = try si.intern(allocator, "Hello");
            const world = try si.intern(allocator, "World");
            const other_hello = try si.intern(allocator, "Hello");
            try std.testing.expectEqual(hello, other_hello);
            try std.testing.expect(hello != world);

            try std.testing.expectEqualStrings("Hello", si.getString(hello));
            try std.testing.expectEqualStrings("World", si.getString(world));
        }
    };
    try std.testing.checkAllAllocationFailures(std.testing.allocator, S.testInterner, .{});
}
