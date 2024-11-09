const std = @import("std");
const Allocator = std.mem.Allocator;
const assert = std.debug.assert;

const aro = @import("aro");
const NodeIndex = aro.Tree.NodeIndex;
const StringId = aro.StringId;

/// map from name to decl node
const Scope = std.AutoHashMapUnmanaged(StringId, NodeIndex);

const Stack = @This();

scopes: std.ArrayListUnmanaged(Scope),
/// allocations from nested scopes are retained after popping; `active_len` is the number
/// of currently-active items in `scopes`.
active_len: usize,

pub const empty: Stack = .{ .scopes = .empty, .active_len = 0 };

pub fn push(s: *Stack, gpa: Allocator) !void {
    if (s.active_len + 1 > s.scopes.items.len) {
        try s.scopes.append(gpa, .{});
        s.active_len = s.scopes.items.len;
    } else {
        s.scopes.items[s.active_len].clearRetainingCapacity();
        s.active_len += 1;
    }
}

pub fn deinit(s: *Stack, gpa: Allocator) void {
    assert(s.active_len == 0);
    for (s.scopes.items) |*scope| {
        scope.deinit(gpa);
    }
    s.scopes.deinit(gpa);
}

pub fn pop(s: *Stack) void {
    s.active_len -= 1;
}

pub fn addSymbol(s: *Stack, gpa: Allocator, name: StringId, decl_node: NodeIndex) !void {
    return s.scopes.items[s.active_len - 1].putNoClobber(gpa, name, decl_node);
}

pub fn getDeclNode(s: *const Stack, name: StringId) NodeIndex {
    var i = s.active_len;
    while (i > 0) {
        i -= 1;
        const node = s.scopes.items[i].get(name) orelse continue;
        return node;
    }
    unreachable;
}
