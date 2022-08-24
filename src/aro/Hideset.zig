const std = @import("std");
const mem = std.mem;
const Allocator = mem.Allocator;
const Source = @import("Source.zig");
const Compilation = @import("Compilation.zig");
const Tokenizer = @import("Tokenizer.zig");

pub const Hideset = @This();

const HashContext = struct {
    pub fn hash(ctx: HashContext, key: Identifier) u64 {
        _ = ctx;
        const val = (@as(u64, @intFromEnum(key.id)) << 32) + key.byte_offset;
        return std.hash.murmur.Murmur2_64.hashUint64(val);
    }
    pub fn eql(ctx: HashContext, a: Identifier, b: Identifier) bool {
        _ = ctx;
        return a.id == b.id and a.byte_offset == b.byte_offset;
    }
};

const Identifier = struct {
    id: Source.Id = .unused,
    byte_offset: u32 = 0,

    fn slice(self: Identifier, comp: *const Compilation) []const u8 {
        var tmp_tokenizer = Tokenizer{
            .buf = comp.getSource(self.id).buf,
            .langopts = comp.langopts,
            .index = self.byte_offset,
            .source = .generated,
        };
        const res = tmp_tokenizer.next();
        return tmp_tokenizer.buf[res.start..res.end];
    }
};

const Item = struct {
    name: Identifier = .{},
    next: Index = Sentinel,
};

const Index = u32;
const Sentinel = std.math.maxInt(Index);

map: std.HashMapUnmanaged(Identifier, Index, HashContext, std.hash_map.default_max_load_percentage),
intersection_map: std.StringHashMapUnmanaged(void),
slab: []Item,
next_idx: Index,
comp: *const Compilation,

const Iterator = struct {
    hideset: *const Hideset,
    i: Index,

    fn next(self: *Iterator) ?Item {
        if (self.i == Sentinel) return null;
        const item = self.hideset.slab[self.i];
        defer self.i = item.next;
        return item;
    }
};

pub fn init(comp: *const Compilation) Hideset {
    return Hideset{
        .comp = comp,
        .map = .{},
        .intersection_map = .{},
        .slab = &.{},
        .next_idx = 0,
    };
}

pub fn deinit(self: *Hideset) void {
    self.map.deinit(self.comp.gpa);
    self.intersection_map.deinit(self.comp.gpa);
    self.comp.gpa.free(self.slab);
}

pub fn clearRetainingCapacity(self: *Hideset) void {
    self.next_idx = 0;
    self.map.clearRetainingCapacity();
}

pub fn iterator(self: *const Hideset, idx: Index) Iterator {
    return Iterator{
        .hideset = self,
        .i = idx,
    };
}

pub fn get(self: *const Hideset, name: Identifier) Index {
    return self.map.get(name) orelse Sentinel;
}

pub fn put(self: *Hideset, key: Identifier, value: Index) !void {
    try self.map.put(self.comp.gpa, key, value);
}

pub fn ensureTotalCapacity(self: *Hideset, new_size: usize) !void {
    var better_size = self.slab.len;
    if (better_size >= new_size) return;

    while (true) {
        better_size = better_size * 2 + 8;
        if (better_size >= new_size) break;
    }
    self.slab = try self.comp.gpa.realloc(self.slab, better_size);
}

fn allocate(self: *Hideset, name: Identifier) !Index {
    try self.ensureTotalCapacity(self.next_idx + 1);
    defer self.next_idx += 1;
    self.slab[self.next_idx] = .{ .name = name, .next = Sentinel };
    return self.next_idx;
}

pub fn prepend(self: *Hideset, name: Identifier, tail: Index) !Index {
    const new_idx = try self.allocate(name);
    self.slab[new_idx].next = tail;
    return new_idx;
}

/// Copy a, then attach b at the end
pub fn @"union"(self: *Hideset, a: Index, b: Index) !Index {
    var cur: Index = Sentinel;
    var head: Index = b;
    var it = self.iterator(a);
    while (it.next()) |item| {
        const new_idx = try self.allocate(item.name);
        if (head == b) {
            head = new_idx;
        }
        if (cur != Sentinel) {
            self.slab[cur].next = new_idx;
        }
        cur = new_idx;
    }
    if (cur != Sentinel) {
        self.slab[cur].next = b;
    }
    return head;
}

pub fn contains(self: *const Hideset, list: Index, name: []const u8) bool {
    var it = self.iterator(list);
    while (it.next()) |item| {
        const this = item.name.slice(self.comp);
        if (mem.eql(u8, name, this)) return true;
    }
    return false;
}

pub fn intersection(self: *Hideset, a: Index, b: Index) !Index {
    if (a == Sentinel or b == Sentinel) return Sentinel;
    self.intersection_map.clearRetainingCapacity();

    var cur: Index = Sentinel;
    var head: Index = Sentinel;
    var it = self.iterator(a);
    while (it.next()) |item| {
        const str = item.name.slice(self.comp);
        try self.intersection_map.put(self.comp.gpa, str, {});
    }
    it = self.iterator(b);
    while (it.next()) |item| {
        const str = item.name.slice(self.comp);
        if (self.intersection_map.contains(str)) {
            const new_idx = try self.allocate(item.name);
            if (head == Sentinel) {
                head = new_idx;
            }
            if (cur != Sentinel) {
                self.slab[cur].next = new_idx;
            }
            cur = new_idx;
        }
    }
    return head;
}
