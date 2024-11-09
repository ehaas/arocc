const std = @import("std");

const aro = @import("aro");
const Compilation = aro.Compilation;
const NodeIndex = Tree.NodeIndex;
const Tree = aro.Tree;
const Type = aro.Type;

const GP_MAX = 6;
const FP_MAX = 8;

const CallConv = @This();

/// Structs or unions equal or smaller than 16 bytes are passed
/// using up to two registers.
///
/// If the first 8 bytes contains only floating-point type members,
/// they are passed in an XMM register. Otherwise, they are passed
/// in a general-purpose register.
///
/// If a struct/union is larger than 8 bytes, the same rule is
/// applied to the the next 8 byte chunk.
///
/// This function returns true if `ty` has only floating-point
/// members in its byte range [lo, hi).
fn hasFlonum(ty: Type, lo: u32, hi: u32, offset: u32) bool {
    if (ty.getRecord()) |record| {
        _ = record;
    } else if (ty.isArray()) {}

    //   if (ty->kind == TY_STRUCT || ty->kind == TY_UNION) {
    //     for (Member *mem = ty->members; mem; mem = mem->next)
    //       if (!has_flonum(mem->ty, lo, hi, offset + mem->offset))
    //         return false;
    //     return true;
    //   }

    //   if (ty->kind == TY_ARRAY) {
    //     for (int i = 0; i < ty->array_len; i++)
    //       if (!has_flonum(ty->base, lo, hi, offset + ty->base->size * i))
    //         return false;
    //     return true;
    //   }

    return offset < lo or hi <= offset or ty.is(.float) or ty.is(.double);
}

fn hasFlonum1(ty: Type) bool {
    return hasFlonum(ty, 0, 8, 0);
}

fn hasFlonum2(ty: Type) bool {
    return hasFlonum(ty, 8, 16, 0);
}

gp_count: u8,
fp_count: u8,
stack: u32,
params: []const Param,

pub const Param = packed struct(u32) {
    pass_by_stack: bool,
    stack_offset: u31,
};

pub const ParamsOrArgs = union(enum) {
    params: []const Type.Func.Param,
    args: []const NodeIndex,

    const Iterator = struct {
        i: usize,
        params_or_args: ParamsOrArgs,
        node_ty: []const Type,

        fn next(self: *Iterator) ?Type {
            defer self.i += 1;
            switch (self.params_or_args) {
                .params => |params| {
                    if (self.i < params.len) return params[self.i].ty.canonicalize(.standard);
                    return null;
                },
                .args => |args| {
                    if (self.i < args.len) return self.node_ty[@intFromEnum(args[self.i])].canonicalize(.standard);
                    return null;
                },
            }
        }
    };

    pub fn iterator(self: ParamsOrArgs, node_ty: []const Type) Iterator {
        return .{ .i = 0, .params_or_args = self, .node_ty = node_ty };
    }

    fn len(self: ParamsOrArgs) usize {
        return switch (self) {
            .params => |params| params.len,
            .args => |args| args.len,
        };
    }
};

/// Iterate over args or params
pub fn compute(iterator: ParamsOrArgs.Iterator, return_by_stack: bool, comp: *const Compilation, result: []Param) !CallConv {
    var stack: u31 = 0;
    var gp: u32 = @intFromBool(return_by_stack);
    var fp: u32 = 0;
    var it = iterator;
    var i: usize = 0;
    while (it.next()) |ty| : (i += 1) {
        const size = ty.sizeof(comp).?;
        switch (ty.specifier) {
            .@"struct",
            .@"union",
            => {
                if (size <= 16) {
                    const fp_inc: u32 = @intFromBool(hasFlonum1(ty)) + @intFromBool(size > 8 and hasFlonum2(ty));
                    const gp_inc: u32 = @intFromBool(!hasFlonum1(ty)) + @intFromBool(size > 8 and !hasFlonum2(ty));

                    if ((fp_inc == 0 or (fp + fp_inc <= FP_MAX)) and (gp_inc == 0 or (gp + gp_inc <= GP_MAX))) {
                        fp += fp_inc;
                        gp += gp_inc;
                        continue;
                    }
                }
            },
            .float, .double => {
                defer fp += 1;
                if (fp < FP_MAX) continue;
            },
            .long_double => {},
            else => {
                defer gp += 1;
                if (gp < GP_MAX) continue;
            },
        }
        result[i].pass_by_stack = true;
        const param_align = ty.alignof(comp);
        if (param_align > 8) {
            stack = std.mem.alignForward(u31, stack, param_align);
        }
        result[i].stack_offset = stack;
        stack += std.mem.alignForward(u31, @intCast(size), 8);
    }
    return .{
        .gp_count = @min(gp, GP_MAX),
        .fp_count = @min(fp, FP_MAX),
        .stack = stack,
        .params = result[0..i],
    };
}
