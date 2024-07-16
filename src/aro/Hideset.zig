//! A hideset is a linked list (implemented as an array so that elements are identified by 4-byte indices)
//! of the set of identifiers from which a token was expanded.
//! During macro expansion, if a token would otherwise be expanded, but its hideset contains
//! the token itself, then it is not expanded
//! Most tokens have an empty hideset, and the hideset is not needed once expansion is complete,
//! so we use a hash map to store them instead of directly storing them with the token.
//! The C standard underspecifies the algorithm for updating a token's hideset;
//! we use the one here: https://www.spinellis.gr/blog/20060626/cpp.algo.pdf

const std = @import("std");
const mem = std.mem;
const Allocator = mem.Allocator;
const Source = @import("Source.zig");
const Compilation = @import("Compilation.zig");
const Tokenizer = @import("Tokenizer.zig");
const Treap = @import("Treap.zig");

pub const Hideset = @This();

const Identifier = struct {
    id: Source.Id = .unused,
    byte_offset: u32 = 0,

    fn fromLocation(loc: Source.Location) Identifier {
        return .{
            .id = loc.id,
            .byte_offset = loc.byte_offset,
        };
    }
};


map: std.AutoHashMapUnmanaged(Identifier, Treap.Node) = .{},
comp: *const Compilation,

pub fn deinit(self: *Hideset) void {
    self.map.deinit(self.comp.gpa);
}

pub fn clearRetainingCapacity(self: *Hideset) void {
    self.map.clearRetainingCapacity();
}

pub fn get(self: *const Hideset, loc: Source.Location) Treap.Node {
    return self.map.get(Identifier.fromLocation(loc)) orelse null;
}

pub fn put(self: *Hideset, loc: Source.Location, value: Treap.Node) !void {
    try self.map.put(self.comp.gpa, Identifier.fromLocation(loc), value);
}
