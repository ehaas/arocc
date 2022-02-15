map: std.AutoArrayHashMapUnmanaged(void, void) = .{},
items: std.MultiArrayList(Item) = .{},
extra: std.ArrayListUnmanaged(u32) = .{},

const InternArena = @This();
const std = @import("std");
const Allocator = std.mem.Allocator;
const assert = std.debug.assert;
const Tree = @import("Tree.zig");
const TokenIndex = Tree.TokenIndex;
const NodeIndex = Tree.NodeIndex;

const KeyAdapter = struct {
    intern_arena: *const InternArena,

    pub fn eql(ctx: @This(), a: Key, b_void: void, b_map_index: usize) bool {
        _ = b_void;
        return ctx.intern_arena.indexToKey(@intToEnum(Index, b_map_index)).eql(a, ctx.intern_arena);
    }

    pub fn hash(ctx: @This(), a: Key) u32 {
        _ = ctx;
        return a.hash();
    }
};

const Range = packed struct {
    /// Start index of underlying slice in `extra`
    start: u32,
    /// len of underlying slice, not total number of `extra` entries
    len: u32,
};

/// Represents a slice of T's using N + 1 words in `extra`
/// First entry is the length; followed by N * sizeInWords(T) elements
fn RangeOf(comptime T: type) type {
    return union {
        const Value = T;
        slice: []const T,
        range: Range,

        fn at(self: @This(), ia: *const InternArena, idx: u32) T {
            assert(idx < self.range.len);
            const extraIndex = self.range.start + idx * sizeInWords(T);
            return ia.extraData(T, extraIndex);
        }
    };
}

fn isRangeOf(comptime T: type) bool {
    return @typeInfo(T) == .Union and @hasDecl(T, "Value");
}

pub const Param = struct {
    ty: Index,
    name_tok: TokenIndex,
};

pub const Array = struct {
    elem: Index,
    len: u64,
};

pub const Expr = struct {
    node: NodeIndex,
    ty: Index,
};

pub const Func = struct {
    return_type: Index,
    params: RangeOf(Param),
};

pub const Key = union(enum) {
    simple: Simple,

    pointer: Index,
    unspecified_variable_len_array: Index,
    decayed_unspecified_variable_len_array: Index,
    typeof_type: Index,

    func: Func,
    array: Array,
    decayed_array: Array,
    static_array: Array,
    decayed_static_array: Array,
    incomplete_array: Array,
    decayed_incomplete_array: Array,

    variable_len_array: Expr,
    decayed_variable_len_array: Expr,
    typeof_expr: Expr,

    pub fn hash(key: Key) u32 {
        var hasher = std.hash.Wyhash.init(0);
        switch (key) {
            .simple => |simple_type| {
                std.hash.autoHash(&hasher, simple_type);
            },
            .pointer, .unspecified_variable_len_array, .decayed_unspecified_variable_len_array, .typeof_type => |sub_type| {
                std.hash.autoHash(&hasher, sub_type);
            },
            .func => |func| {
                std.hash.autoHash(&hasher, func.return_type);
                for (func.params.slice) |param| {
                    std.hash.autoHash(&hasher, param.name_tok);
                    std.hash.autoHash(&hasher, param.ty);
                }
            },
            .array, .decayed_array, .static_array, .decayed_static_array, .incomplete_array, .decayed_incomplete_array => |array| {
                std.hash.autoHash(&hasher, array.elem);
                std.hash.autoHash(&hasher, array.len);
            },
            .variable_len_array, .decayed_variable_len_array, .typeof_expr => |var_array| {
                std.hash.autoHash(&hasher, var_array.node);
                std.hash.autoHash(&hasher, var_array.ty);
            },
        }
        return @truncate(u32, hasher.final());
    }

    pub fn eql(a: Key, b: Key, ia: *const InternArena) bool {
        const KeyTag = std.meta.Tag(Key);
        const a_tag: KeyTag = a;
        const b_tag: KeyTag = b;
        if (a_tag != b_tag) return false;
        switch (a) {
            .simple => return a.simple == b.simple,
            .pointer => return a.pointer == b.pointer,
            .unspecified_variable_len_array => return a.unspecified_variable_len_array == b.unspecified_variable_len_array,
            .decayed_unspecified_variable_len_array => return a.decayed_unspecified_variable_len_array == b.decayed_unspecified_variable_len_array,
            .typeof_type => return a.typeof_type == b.typeof_type,
            .func => {
                if (a.func.return_type != b.func.return_type) return false;
                if (a.func.params.range.len != b.func.params.slice.len) return false;
                for (b.func.params.slice) |param, i| {
                    const val = a.func.params.at(ia, @intCast(u32, i));
                    if (!std.meta.eql(param, val)) return false;
                }
                return true;
            },
            .array => return a.array.elem == b.array.elem and a.array.len == b.array.len,
            .decayed_array => return a.decayed_array.elem == b.decayed_array.elem and a.decayed_array.len == b.decayed_array.len,
            .static_array => return a.static_array.elem == b.static_array.elem and a.static_array.len == b.static_array.len,
            .decayed_static_array => return a.decayed_static_array.elem == b.decayed_static_array.elem and a.decayed_static_array.len == b.decayed_static_array.len,
            .incomplete_array => return a.incomplete_array.elem == b.incomplete_array.elem and a.incomplete_array.len == b.incomplete_array.len,
            .decayed_incomplete_array => return a.decayed_incomplete_array.elem == b.decayed_incomplete_array.elem and a.decayed_incomplete_array.len == b.decayed_incomplete_array.len,
            .variable_len_array => return a.variable_len_array.node == b.variable_len_array.node and a.variable_len_array.ty == b.variable_len_array.ty,
            .decayed_variable_len_array => return a.decayed_variable_len_array.node == b.decayed_variable_len_array.node and a.decayed_variable_len_array.ty == b.decayed_variable_len_array.ty,
            .typeof_expr => return a.typeof_expr.node == b.typeof_expr.node and a.typeof_expr.ty == b.typeof_expr.ty,
        }
    }
};

pub const Item = struct {
    tag: Tag,
    /// The doc comments on the respective Tag explain how to interpret this.
    data: u32,
};

/// Represents an index into `map`. It represents the canonical index
/// of a `Value` within this `InternArena`. The values are typed.
/// Two values which have the same type can be equality compared simply
/// by checking if their indexes are equal, provided they are both in
/// the same `InternArena`.
pub const Index = enum(u32) {
    none = std.math.maxInt(u32),
    _,

    pub fn isLocalConstQualified(self: Index) bool {
        return @enumToInt(self) & (1 << 31) != 0;
    }

    pub fn isLocalVolatileQualified(self: Index) bool {
        return @enumToInt(self) & (1 << 30) != 0;
    }

    pub fn isLocalRestrictQualified(self: Index) bool {
        return @enumToInt(self) & (1 << 29) != 0;
    }

    pub fn isLocalExtendedQualified(self: Index) bool {
        return @enumToInt(self) & (1 << 28) != 0;
    }

    pub fn unqualified(self: Index) Index {
        return @enumToInt(self) & 0xFFF_FFFF;
    }
};

pub const Tag = enum(u8) {
    /// A type or value that can be represented with only an enum tag.
    /// data is Simple enum value
    simple,

    /// A type wrapper
    /// data is Index of subtype
    pointer,
    unspecified_variable_len_array,
    decayed_unspecified_variable_len_array,
    typeof_type,

    /// A function
    /// data is index of Func in `extra`
    func,

    /// An array
    /// data is index of Array in `extra`
    array,
    decayed_array,
    static_array,
    decayed_static_array,
    incomplete_array,
    decayed_incomplete_array,

    // data.expr
    variable_len_array,
    decayed_variable_len_array,
    typeof_expr,
};

pub const Simple = enum(u32) {
    void,
    bool,

    // integers
    char,
    schar,
    uchar,
    short,
    ushort,
    int,
    uint,
    long,
    ulong,
    long_long,
    ulong_long,

    // floating point numbers
    float,
    double,
    long_double,
    complex_float,
    complex_double,
    complex_long_double,
};

pub fn deinit(ia: *InternArena, gpa: Allocator) void {
    ia.map.deinit(gpa);
    ia.items.deinit(gpa);
    ia.extra.deinit(gpa);
}

pub fn indexToKey(ia: InternArena, index: Index) Key {
    const item = ia.items.get(@enumToInt(index));
    const data = item.data;
    return switch (item.tag) {
        .simple => .{ .simple = @intToEnum(Simple, data) },
        .pointer => .{ .pointer = @intToEnum(Index, data) },
        .unspecified_variable_len_array => .{ .unspecified_variable_len_array = @intToEnum(Index, data) },
        .decayed_unspecified_variable_len_array => .{ .decayed_unspecified_variable_len_array = @intToEnum(Index, data) },
        .typeof_type => .{ .typeof_type = @intToEnum(Index, data) },
        .func => {
            const func_info = ia.extraData(Func, data);
            return .{
                .func = .{
                    .return_type = func_info.return_type,
                    .params = func_info.params,
                },
            };
        },
        .array => {
            const array_info = ia.extraData(Array, data);
            return .{ .array = .{
                .elem = array_info.elem,
                .len = array_info.len,
            } };
        },
        .decayed_array => {
            const array_info = ia.extraData(Array, data);
            return .{ .decayed_array = .{
                .elem = array_info.elem,
                .len = array_info.len,
            } };
        },
        .static_array => {
            const array_info = ia.extraData(Array, data);
            return .{ .static_array = .{
                .elem = array_info.elem,
                .len = array_info.len,
            } };
        },
        .decayed_static_array => {
            const array_info = ia.extraData(Array, data);
            return .{ .decayed_static_array = .{
                .elem = array_info.elem,
                .len = array_info.len,
            } };
        },
        .incomplete_array => {
            const array_info = ia.extraData(Array, data);
            return .{ .incomplete_array = .{
                .elem = array_info.elem,
                .len = array_info.len,
            } };
        },
        .decayed_incomplete_array => {
            const array_info = ia.extraData(Array, data);
            return .{ .decayed_incomplete_array = .{
                .elem = array_info.elem,
                .len = array_info.len,
            } };
        },
        .variable_len_array => {
            const array_info = ia.extraData(Expr, data);
            return .{ .variable_len_array = .{
                .node = array_info.node,
                .ty = array_info.ty,
            } };
        },
        .decayed_variable_len_array => {
            const array_info = ia.extraData(Expr, data);
            return .{ .decayed_variable_len_array = .{
                .node = array_info.node,
                .ty = array_info.ty,
            } };
        },
        .typeof_expr => {
            const array_info = ia.extraData(Expr, data);
            return .{ .typeof_expr = .{
                .node = array_info.node,
                .ty = array_info.ty,
            } };
        },
    };
}

pub fn get(ia: *InternArena, gpa: Allocator, key: Key) Allocator.Error!Index {
    const adapter: KeyAdapter = .{ .intern_arena = ia };
    const gop = try ia.map.getOrPutAdapted(gpa, key, adapter);
    if (gop.found_existing) {
        return @intToEnum(Index, gop.index);
    }
    switch (key) {
        .simple => |simple_type| {
            try ia.items.append(gpa, .{
                .tag = .simple,
                .data = @enumToInt(simple_type),
            });
        },
        .pointer => |pointer_type| {
            try ia.items.append(gpa, .{
                .tag = .pointer,
                .data = @enumToInt(pointer_type),
            });
        },
        .unspecified_variable_len_array => |unspecified_type| {
            try ia.items.append(gpa, .{
                .tag = .unspecified_variable_len_array,
                .data = @enumToInt(unspecified_type),
            });
        },
        .decayed_unspecified_variable_len_array => |decayed_type| {
            try ia.items.append(gpa, .{
                .tag = .decayed_unspecified_variable_len_array,
                .data = @enumToInt(decayed_type),
            });
        },
        .typeof_type => |typeof_type| {
            try ia.items.append(gpa, .{
                .tag = .typeof_type,
                .data = @enumToInt(typeof_type),
            });
        },
        .func => |func_type| {
            try ia.items.append(gpa, .{
                .tag = .func,
                .data = try ia.addExtra(gpa, Func{
                    .return_type = func_type.return_type,
                    .params = func_type.params,
                }),
            });
        },
        .array => |array_type| {
            try ia.items.append(gpa, .{
                .tag = .array,
                .data = try ia.addExtra(gpa, Array{
                    .elem = array_type.elem,
                    .len = array_type.len,
                }),
            });
        },
        .decayed_array => |array_type| {
            try ia.items.append(gpa, .{
                .tag = .decayed_array,
                .data = try ia.addExtra(gpa, Array{
                    .elem = array_type.elem,
                    .len = array_type.len,
                }),
            });
        },
        .static_array => |array_type| {
            try ia.items.append(gpa, .{
                .tag = .static_array,
                .data = try ia.addExtra(gpa, Array{
                    .elem = array_type.elem,
                    .len = array_type.len,
                }),
            });
        },
        .decayed_static_array => |array_type| {
            try ia.items.append(gpa, .{
                .tag = .decayed_static_array,
                .data = try ia.addExtra(gpa, Array{
                    .elem = array_type.elem,
                    .len = array_type.len,
                }),
            });
        },
        .incomplete_array => |array_type| {
            try ia.items.append(gpa, .{
                .tag = .incomplete_array,
                .data = try ia.addExtra(gpa, Array{
                    .elem = array_type.elem,
                    .len = array_type.len,
                }),
            });
        },
        .decayed_incomplete_array => |array_type| {
            try ia.items.append(gpa, .{
                .tag = .decayed_incomplete_array,
                .data = try ia.addExtra(gpa, Array{
                    .elem = array_type.elem,
                    .len = array_type.len,
                }),
            });
        },
        .variable_len_array => |var_array| {
            try ia.items.append(gpa, .{
                .tag = .variable_len_array,
                .data = try ia.addExtra(gpa, Expr{
                    .node = var_array.node,
                    .ty = var_array.ty,
                }),
            });
        },
        .decayed_variable_len_array => |var_array| {
            try ia.items.append(gpa, .{
                .tag = .decayed_variable_len_array,
                .data = try ia.addExtra(gpa, Expr{
                    .node = var_array.node,
                    .ty = var_array.ty,
                }),
            });
        },
        .typeof_expr => |typeof_expr| {
            try ia.items.append(gpa, .{
                .tag = .typeof_expr,
                .data = try ia.addExtra(gpa, Expr{
                    .node = typeof_expr.node,
                    .ty = typeof_expr.ty,
                }),
            });
        },
    }
    return @intToEnum(Index, ia.items.len - 1);
}

/// number of u32's required to store T
fn sizeInWords(comptime T: type) u32 {
    assert(T != Range and !isRangeOf(T));
    switch (T) {
        u32, i32, Index, NodeIndex => return 1,
        u64 => @compileError("u64 is variable length and requires value for encoding"),
        else => {
            var size: u32 = 0;
            inline for (std.meta.fields(T)) |field| {
                size += sizeInWords(field.field_type);
            }
            return size;
        },
    }
}

fn sizeInWordsForValue(comptime T: type, val: T) u32 {
    return switch (T) {
        u64 => {
            var dest: [3]u32 = undefined;
            return @intCast(u32, encodeLong(val, &dest).len);
        },
        else => sizeInWords(T),
    };
}

fn capacityRequired(extra: anytype) u32 {
    const fields = std.meta.fields(@TypeOf(extra));
    var capacity: u32 = 0;
    inline for (fields) |field| {
        if (comptime isRangeOf(field.field_type)) {
            // TODO: sizeInWordsForValue for each slice element
            const sliceLen = @intCast(u32, @field(extra, field.name).slice.len);
            const fieldSize = sizeInWords(field.field_type.Value);
            capacity += 1 + fieldSize * sliceLen; // length followed by contents
        } else {
            capacity += sizeInWordsForValue(field.field_type, @field(extra, field.name));
        }
    }
    return capacity;
}

fn addExtra(ia: *InternArena, gpa: Allocator, extra: anytype) Allocator.Error!u32 {
    const need = capacityRequired(extra);
    try ia.extra.ensureUnusedCapacity(gpa, need);
    return ia.addExtraAssumeCapacity(extra);
}

fn addRangeAssumeCapacity(ia: *InternArena, range: anytype) void {
    ia.extra.appendAssumeCapacity(@intCast(u32, range.slice.len));
    for (range.slice) |item| {
        _ = ia.addExtraAssumeCapacity(item);
    }
}

fn encodedLength(first_word: u32) u2 {
    return switch (first_word) {
        0...std.math.maxInt(u30) => 1,
        0xFFFF_FFFF => 3,
        else => 2,
    };
}

fn encodeLong(val: u64, dest: []u32) []u32 {
    if (val <= std.math.maxInt(u30)) {
        dest[0] = @intCast(u32, val);
        return dest[0..1];
    } else {
        const high = @intCast(u32, val >> 32);
        const low = @truncate(u32, val);
        if (val <= std.math.maxInt(u62)) {
            dest[0] = high | 0x4000_0000;
            dest[1] = low;
            return dest[0..2];
        } else {
            dest[0] = 0xFFFF_FFFF;
            dest[1] = high;
            dest[2] = low;
            return dest[0..3];
        }
    }
}

fn decodeLong(words: []const u32) u64 {
    if (words[0] <= std.math.maxInt(u30)) return words[0];
    if (words[0] == 0xFFFF_FFFF) return (@as(u64, words[1]) << 32) + words[2];
    return (@as(u64, words[0] & 0x3FFF_FFFF) << 32) + words[1];
}

fn addExtraAssumeCapacity(ia: *InternArena, extra: anytype) u32 {
    const fields = std.meta.fields(@TypeOf(extra));
    const result = @intCast(u32, ia.extra.items.len);
    inline for (fields) |field| {
        if (comptime isRangeOf(field.field_type)) {
            ia.addRangeAssumeCapacity(@field(extra, field.name));
        } else if (field.field_type == u64) {
            var scratch: [3]u32 = undefined;
            for (encodeLong(@field(extra, field.name), &scratch)) |word| {
                ia.extra.appendAssumeCapacity(word);
            }
        } else {
            ia.extra.appendAssumeCapacity(switch (field.field_type) {
                u32 => @field(extra, field.name),
                Index, NodeIndex => @enumToInt(@field(extra, field.name)),
                i32 => @bitCast(u32, @field(extra, field.name)),
                else => @compileError("bad field type"),
            });
        }
    }
    return result;
}

fn extraData(ia: InternArena, comptime T: type, index: u32) T {
    const fields = std.meta.fields(T);
    var i: u32 = index;
    var result: T = undefined;
    inline for (fields) |field| {
        if (comptime isRangeOf(field.field_type)) {
            @field(result, field.name) = .{ .range = .{ .start = i + 1, .len = ia.extra.items[i] } };
            i += @field(result, field.name).range.len + 1;
        } else if (field.field_type == u64) {
            const size = encodedLength(ia.extra.items[i]);
            @field(result, field.name) = decodeLong(ia.extra.items[i .. i + size]);
            i += size;
        } else {
            @field(result, field.name) = switch (field.field_type) {
                u32 => ia.extra.items[i],
                Index => @intToEnum(Index, ia.extra.items[i]),
                NodeIndex => @intToEnum(NodeIndex, ia.extra.items[i]),
                i32 => @bitCast(i32, ia.extra.items[i]),
                else => @compileError("bad field type"),
            };
            i += 1;
        }
    }
    return result;
}

test "basic usage" {
    const gpa = std.testing.allocator;

    var ia: InternArena = .{};
    defer ia.deinit(gpa);

    const int_type = try ia.get(gpa, .{ .simple = .int });
    const long_type = try ia.get(gpa, .{ .simple = .long });

    try std.testing.expect(int_type != long_type);

    const other_int_type = try ia.get(gpa, .{ .simple = .int });

    try std.testing.expectEqual(int_type, other_int_type);

    const int_ptr_type = try ia.get(gpa, .{ .pointer = int_type });
    const other_int_ptr_type = try ia.get(gpa, .{ .pointer = int_type });

    try std.testing.expect(int_ptr_type != int_type);
    try std.testing.expect(int_ptr_type != other_int_type);
    try std.testing.expectEqual(int_ptr_type, other_int_ptr_type);
    try std.testing.expectEqual(ia.indexToKey(int_ptr_type).pointer, int_type);

    const long_array_type_len_42 = try ia.get(gpa, .{ .array = .{ .elem = long_type, .len = 42 } });
    const long_array_type_len_43 = try ia.get(gpa, .{ .array = .{ .elem = long_type, .len = 43 } });

    try std.testing.expect(long_array_type_len_42 != long_array_type_len_43);
    try std.testing.expectEqual(ia.indexToKey(long_array_type_len_42).array.elem, long_type);
    try std.testing.expectEqual(ia.indexToKey(long_array_type_len_43).array.elem, long_type);

    const params = [_]Param{
        Param{ .name_tok = 1, .ty = int_type },
        Param{ .name_tok = 2, .ty = int_ptr_type },
    };
    const my_func_type = try ia.get(gpa, .{
        .func = .{
            .return_type = int_type,
            .params = .{ .slice = &params },
        },
    });
    try std.testing.expectEqual(@as(u32, 2), ia.indexToKey(my_func_type).func.params.range.len);

    const func_one_param = try ia.get(gpa, .{
        .func = .{
            .return_type = int_type,
            .params = .{ .slice = params[1..] },
        },
    });

    try std.testing.expect(my_func_type != func_one_param);
    const func_no_params = try ia.get(gpa, .{
        .func = .{
            .return_type = int_type,
            .params = .{ .slice = &.{} },
        },
    });
    try std.testing.expect(func_no_params != func_one_param);

    const another_func = try ia.get(gpa, .{
        .func = .{
            .return_type = int_type,
            .params = .{ .slice = &params },
        },
    });
    try std.testing.expectEqual(my_func_type, another_func);

    const int_type_again = try ia.get(gpa, .{ .simple = .int });
    try std.testing.expectEqual(int_type_again, ia.indexToKey(func_no_params).func.return_type);

    const large_array = try ia.get(gpa, .{ .array = .{ .elem = int_type, .len = std.math.maxInt(u30) } });
    const larger_array = try ia.get(gpa, .{ .array = .{ .elem = int_type, .len = std.math.maxInt(u30) + 1 } });
    const gigantic_array = try ia.get(gpa, .{ .array = .{ .elem = int_type, .len = std.math.maxInt(u63) } });
    const biggest_array = try ia.get(gpa, .{ .array = .{ .elem = int_type, .len = std.math.maxInt(u64) } });

    try std.testing.expectEqual(@as(u64, std.math.maxInt(u30)), ia.indexToKey(large_array).array.len);
    try std.testing.expectEqual(@as(u64, std.math.maxInt(u30) + 1), ia.indexToKey(larger_array).array.len);
    try std.testing.expectEqual(@as(u64, std.math.maxInt(u63)), ia.indexToKey(gigantic_array).array.len);
    try std.testing.expectEqual(@as(u64, std.math.maxInt(u64)), ia.indexToKey(biggest_array).array.len);
}
