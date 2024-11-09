const std = @import("std");
const Allocator = std.mem.Allocator;
const assert = std.debug.assert;

const aro = @import("aro");
const Assembly = aro.Assembly;
const Compilation = aro.Compilation;
const NodeIndex = Tree.NodeIndex;
const Source = aro.Source;
const Tree = aro.Tree;
const Type = aro.Type;
const Value = aro.Value;

const AsmCodeGen = @This();
const Error = aro.Compilation.Error;
const Writer = std.ArrayListUnmanaged(u8).Writer;

const Scope = @import("Scope.zig");
const CallConv = @import("CallConv.zig");

const GP_MAX = 6;
const FP_MAX = 8;

const i32i8 = "movsbl %al, %eax";
const i32u8 = "movzbl %al, %eax";
const i32i16 = "movswl %ax, %eax";
const i32u16 = "movzwl %ax, %eax";
const i32f32 = "cvtsi2ssl %eax, %xmm0";
const i32i64 = "movslq %eax, %rax";
const i32f64 = "cvtsi2sdl %eax, %xmm0";
const i32f80 = "push %rax; fildl (%rsp); pop %rax";

const u32f32 = "mov %eax, %eax; cvtsi2ssq %rax, %xmm0";
const u32i64 = "mov %eax, %eax";
const u32f64 = "mov %eax, %eax; cvtsi2sdq %rax, %xmm0";
const u32f80 = "mov %eax, %eax; push %rax; fildll (%rsp); pop %rax";

const i64f32 = "cvtsi2ssq %rax, %xmm0";
const i64f64 = "cvtsi2sdq %rax, %xmm0";
const i64f80 = "push %rax; fildll (%rsp); pop %rax";

const u64f32 =
    "test %rax,%rax; js 1f; pxor %xmm0,%xmm0; cvtsi2ss %rax,%xmm0; jmp 2f; " ++
    "1: mov %rax,%rdx; and $1,%eax; pxor %xmm0,%xmm0; shr %rdx; " ++
    "or %rax,%rdx; cvtsi2ss %rdx,%xmm0; addss %xmm0,%xmm0; 2:";
const u64f64 =
    "test %rax,%rax; js 1f; pxor %xmm0,%xmm0; cvtsi2sd %rax,%xmm0; jmp 2f; " ++
    "1: mov %rax,%rdx; and $1,%eax; pxor %xmm0,%xmm0; shr %rdx; " ++
    "or %rax,%rdx; cvtsi2sd %rdx,%xmm0; addsd %xmm0,%xmm0; 2:";
const u64f80 =
    "push %rax; fildq (%rsp); test %rax, %rax; jns 1f;" ++
    "mov $1602224128, %eax; mov %eax, 4(%rsp); fadds 4(%rsp); 1:; pop %rax";

const f32i8 = "cvttss2sil %xmm0, %eax; movsbl %al, %eax";
const f32u8 = "cvttss2sil %xmm0, %eax; movzbl %al, %eax";
const f32i16 = "cvttss2sil %xmm0, %eax; movswl %ax, %eax";
const f32u16 = "cvttss2sil %xmm0, %eax; movzwl %ax, %eax";
const f32i32 = "cvttss2sil %xmm0, %eax";
const f32u32 = "cvttss2siq %xmm0, %rax";
const f32i64 = "cvttss2siq %xmm0, %rax";
const f32u64 =
    "cvttss2siq %xmm0, %rcx; movq %rcx, %rdx; movl $0x5F000000, %eax; " ++
    "movd %eax, %xmm1; subss %xmm1, %xmm0; cvttss2siq %xmm0, %rax; " ++
    "sarq $63, %rdx; andq %rdx, %rax; orq %rcx, %rax;";
const f32f64 = "cvtss2sd %xmm0, %xmm0";
const f32f80 = "sub $8, %rsp; movss %xmm0, (%rsp); flds (%rsp); add $8, %rsp";

const f64i8 = "cvttsd2sil %xmm0, %eax; movsbl %al, %eax";
const f64u8 = "cvttsd2sil %xmm0, %eax; movzbl %al, %eax";
const f64i16 = "cvttsd2sil %xmm0, %eax; movswl %ax, %eax";
const f64u16 = "cvttsd2sil %xmm0, %eax; movzwl %ax, %eax";
const f64i32 = "cvttsd2sil %xmm0, %eax";
const f64u32 = "cvttsd2siq %xmm0, %rax";
const f64i64 = "cvttsd2siq %xmm0, %rax";
const f64u64 =
    "cvttsd2siq %xmm0, %rcx; movq %rcx, %rdx; mov $0x43e0000000000000, %rax; " ++
    "movq %rax, %xmm1; subsd %xmm1, %xmm0; cvttsd2siq %xmm0, %rax; " ++
    "sarq $63, %rdx; andq %rdx, %rax; orq %rcx, %rax";
const f64f32 = "cvtsd2ss %xmm0, %xmm0";
const f64f80 = "sub $8, %rsp; movsd %xmm0, (%rsp); fldl (%rsp); add $8, %rsp";

const FROM_F80_1 =
    "sub $24, %rsp; fnstcw 14(%rsp); movzwl 14(%rsp), %eax; or $12, %ah; " ++
    "mov %ax, 12(%rsp); fldcw 12(%rsp); ";

const FROM_F80_2 = " (%rsp); fldcw 14(%rsp); ";
const FROM_F80_3 = "; add $24, %rsp\n";

const f80i8 = FROM_F80_1 ++ "fistps" ++ FROM_F80_2 ++ "movsbl (%rsp), %eax" ++ FROM_F80_3;
const f80u8 = FROM_F80_1 ++ "fistps" ++ FROM_F80_2 ++ "movzbl (%rsp), %eax" ++ FROM_F80_3;
const f80i16 = FROM_F80_1 ++ "fistps" ++ FROM_F80_2 ++ "movzbl (%rsp), %eax" ++ FROM_F80_3;
const f80u16 = FROM_F80_1 ++ "fistpl" ++ FROM_F80_2 ++ "movswl (%rsp), %eax" ++ FROM_F80_3;
const f80i32 = FROM_F80_1 ++ "fistpl" ++ FROM_F80_2 ++ "mov (%rsp), %eax" ++ FROM_F80_3;
const f80u32 = FROM_F80_1 ++ "fistpl" ++ FROM_F80_2 ++ "mov (%rsp), %eax" ++ FROM_F80_3;
const f80i64 = FROM_F80_1 ++ "fistpq" ++ FROM_F80_2 ++ "mov (%rsp), %rax" ++ FROM_F80_3;
const f80u64 =
    "sub $16, %rsp; movl $0x5f000000, 12(%rsp); flds 12(%rsp); fucomi %st(1), %st; setbe %al;" ++
    "fldz; fcmovbe %st(1), %st; fstp %st(1); fsubrp %st, %st(1); fnstcw 4(%rsp);" ++
    "movzwl 4(%rsp), %ecx; orl $3072, %ecx; movw %cx, 6(%rsp); fldcw 6(%rsp);" ++
    "fistpll 8(%rsp); fldcw 4(%rsp); shlq $63, %rax; xorq 8(%rsp), %rax; add $16, %rsp\n";

const f80f32 = "sub $8, %rsp; fstps (%rsp); movss (%rsp), %xmm0; add $8, %rsp\n";
const f80f64 = "sub $8, %rsp; fstpl (%rsp); movsd (%rsp), %xmm0; add $8, %rsp\n";

// zig fmt: off
const cast_table = [_][11]?[]const u8{
//  i8     i16     i32     i64     u8     u16     u32     u64     f32     f64     f80
  .{null,  null,   null,   i32i64, i32u8, i32u16, null,   i32i64, i32f32, i32f64, i32f80}, // i8
  .{i32i8, null,   null,   i32i64, i32u8, i32u16, null,   i32i64, i32f32, i32f64, i32f80}, // i16
  .{i32i8, i32i16, null,   i32i64, i32u8, i32u16, null,   i32i64, i32f32, i32f64, i32f80}, // i32
  .{i32i8, i32i16, null,   null,   i32u8, i32u16, null,   null,   i64f32, i64f64, i64f80}, // i64

  .{i32i8, null,   null,   i32i64, null,  null,   null,   i32i64, i32f32, i32f64, i32f80}, // u8
  .{i32i8, i32i16, null,   i32i64, i32u8, null,   null,   i32i64, i32f32, i32f64, i32f80}, // u16
  .{i32i8, i32i16, null,   u32i64, i32u8, i32u16, null,   u32i64, u32f32, u32f64, u32f80}, // u32
  .{i32i8, i32i16, null,   null,   i32u8, i32u16, null,   null,   u64f32, u64f64, u64f80}, // u64

  .{f32i8, f32i16, f32i32, f32i64, f32u8, f32u16, f32u32, f32u64, null,   f32f64, f32f80}, // f32
  .{f64i8, f64i16, f64i32, f64i64, f64u8, f64u16, f64u32, f64u64, f64f32, null,   f64f80}, // f64
  .{f80i8, f80i16, f80i32, f80i64, f80u8, f80u16, f80u32, f80u64, f80f32, f80f64, null},   // f80
};
// zig fmt: on

tree: Tree,
comp: *Compilation,
node_tag: []const Tree.Tag,
node_data: []const Tree.Node.Data,
node_ty: []const Type,
node_loc: []const Tree.Node.Loc,
text: Writer,
data: Writer,
va_gp_start: i32,
va_fp_start: i32,
va_st_start: u32,
vla_base_ofs: i32,
rtn_ptr_ofs: i32,
lvar_stk_sz: i32,
peak_stk_usage: i32,
count: u32,
dont_reuse_stack: bool,
tmp_stk: std.ArrayListUnmanaged(i32),
call_conv: std.ArrayListUnmanaged(CallConv.Param),
/// Todo: proper scope management
ofs: std.AutoHashMapUnmanaged(NodeIndex, i32),
scope: Scope,
current_fn_params: std.AutoArrayHashMapUnmanaged(aro.StringId, i32),

const argreg8 = [_][]const u8{ "%dil", "%sil", "%dl", "%cl", "%r8b", "%r9b" };
const argreg16 = [_][]const u8{ "%di", "%si", "%dx", "%cx", "%r8w", "%r9w" };
const argreg32 = [_][]const u8{ "%edi", "%esi", "%edx", "%ecx", "%r8d", "%r9d" };
const argreg64 = [_][]const u8{ "%rdi", "%rsi", "%rdx", "%rcx", "%r8", "%r9" };

const StorageUnit = enum(u8) {
    byte = 8,
    short = 16,
    long = 32,
    quad = 64,

    fn trunc(self: StorageUnit, val: u64) u64 {
        return switch (self) {
            .byte => @as(u8, @truncate(val)),
            .short => @as(u16, @truncate(val)),
            .long => @as(u32, @truncate(val)),
            .quad => val,
        };
    }
};

fn serializeInt(value: u64, storage_unit: StorageUnit, w: Writer) !void {
    try w.print("  .{s}  0x{x}\n", .{ @tagName(storage_unit), storage_unit.trunc(value) });
}

fn serializeFloat(comptime T: type, value: T, w: Writer) !void {
    switch (T) {
        f128 => {
            const bytes = std.mem.asBytes(&value);
            const first = std.mem.bytesToValue(u64, bytes[0..8]);
            try serializeInt(first, .quad, w);
            const second = std.mem.bytesToValue(u64, bytes[8..16]);
            return serializeInt(second, .quad, w);
        },
        f80 => {
            const bytes = std.mem.asBytes(&value);
            const first = std.mem.bytesToValue(u64, bytes[0..8]);
            try serializeInt(first, .quad, w);
            const second = std.mem.bytesToValue(u16, bytes[8..10]);
            try serializeInt(second, .short, w);
            return w.writeAll("  .zero 6\n");
        },
        else => {
            const size = @bitSizeOf(T);
            const storage_unit = std.meta.intToEnum(StorageUnit, size) catch unreachable;
            const IntTy = @Type(.{ .int = .{ .signedness = .unsigned, .bits = size } });
            const int_val: IntTy = @bitCast(value);
            return serializeInt(int_val, storage_unit, w);
        },
    }
}

pub fn todoNode(c: *AsmCodeGen, msg: []const u8, node: NodeIndex) Error {
    const loc: Source.Location = c.tree.nodeLoc(node) orelse .{};

    try c.comp.addDiagnostic(.{
        .tag = .todo,
        .loc = loc,
        .extra = .{ .str = msg },
    }, &.{});
    return error.FatalError;
}

pub fn todoTok(c: *AsmCodeGen, msg: []const u8, tok: Tree.TokenIndex) Error {
    try c.comp.addDiagnostic(.{
        .tag = .todo,
        .loc = c.tree.tokens.items(.loc)[tok],
        .extra = .{ .str = msg },
    }, &.{});
    return error.FatalError;
}

fn emitAggregate(c: *AsmCodeGen, ty: Type, node: NodeIndex) !void {
    _ = ty;
    return c.todoNode("Codegen aggregates", node);
}

fn emitSingleValue(c: *AsmCodeGen, ty: Type, node: NodeIndex) !void {
    const value = c.tree.value_map.get(node) orelse return;
    const bit_size = ty.bitSizeof(c.comp).?;
    if (ty.isComplex()) {
        return c.todoNode("Codegen _Complex values", node);
    } else if (ty.isInt()) {
        const storage_unit = std.meta.intToEnum(StorageUnit, bit_size) catch return c.todoNode("Codegen _BitInt values", node);
        try c.data.print("  .{s} ", .{@tagName(storage_unit)});
        _ = try value.print(ty, c.comp, c.data);
        try c.data.writeByte('\n');
    } else if (ty.isFloat()) {
        switch (bit_size) {
            16 => return serializeFloat(f16, value.toFloat(f16, c.comp), c.data),
            32 => return serializeFloat(f32, value.toFloat(f32, c.comp), c.data),
            64 => return serializeFloat(f64, value.toFloat(f64, c.comp), c.data),
            80 => return serializeFloat(f80, value.toFloat(f80, c.comp), c.data),
            128 => return serializeFloat(f128, value.toFloat(f128, c.comp), c.data),
            else => unreachable,
        }
    } else if (ty.isPtr()) {
        return c.todoNode("Codegen pointer", node);
    } else if (ty.isArray()) {
        // Todo:
        //  Handle truncated initializers e.g. char x[3] = "hello";
        //  Zero out remaining bytes if initializer is shorter than storage capacity
        //  Handle non-char strings
        const bytes = value.toBytes(c.comp);
        const directive = if (bytes.len > bit_size / 8) "ascii" else "string";
        try c.data.print("  .{s} ", .{directive});
        try Value.printString(bytes, ty, c.comp, c.data);

        try c.data.writeByte('\n');
    } else unreachable;
}

fn emitValue(c: *AsmCodeGen, ty: Type, node: NodeIndex) !void {
    const tag = c.node_tag[@intFromEnum(node)];
    switch (tag) {
        .array_init_expr,
        .array_init_expr_two,
        .struct_init_expr,
        .struct_init_expr_two,
        .union_init_expr,
        => return c.todoNode("Codegen multiple inits", node),
        else => return c.emitSingleValue(ty, node),
    }
}

fn deinit(c: *AsmCodeGen) void {
    c.call_conv.deinit(c.comp.gpa);
    c.ofs.deinit(c.comp.gpa);
    c.scope.deinit(c.comp.gpa);
    c.current_fn_params.deinit(c.comp.gpa);
    c.tmp_stk.deinit(c.comp.gpa);
}

pub fn genAsm(tree: Tree) Error!Assembly {
    var data: std.ArrayListUnmanaged(u8) = .empty;
    defer data.deinit(tree.comp.gpa);

    var text: std.ArrayListUnmanaged(u8) = .empty;
    defer text.deinit(tree.comp.gpa);

    const node_tag = tree.nodes.items(.tag);
    var codegen: AsmCodeGen = .{
        .tree = tree,
        .comp = tree.comp,
        .node_tag = node_tag,
        .node_data = tree.nodes.items(.data),
        .node_ty = tree.nodes.items(.ty),
        .node_loc = tree.nodes.items(.loc),
        .text = text.writer(tree.comp.gpa),
        .data = data.writer(tree.comp.gpa),
        .va_gp_start = 0,
        .va_fp_start = 0,
        .va_st_start = 0,
        .vla_base_ofs = 0,
        .rtn_ptr_ofs = 0,
        .lvar_stk_sz = 0,
        .peak_stk_usage = 0,
        .dont_reuse_stack = false,
        .call_conv = .empty,
        .ofs = .empty,
        .scope = .empty,
        .count = 0,
        .current_fn_params = .empty,
        .tmp_stk = .empty,
    };
    defer codegen.deinit();

    try codegen.scope.push(tree.comp.gpa);
    defer codegen.scope.pop();

    if (tree.comp.code_gen_options.debug) {
        const sources = tree.comp.sources.values();
        for (sources) |source| {
            try codegen.data.print("  .file {d} \"{s}\"\n", .{ @intFromEnum(source.id) - 1, source.path });
        }
    }

    for (codegen.tree.root_decls) |decl| {
        switch (node_tag[@intFromEnum(decl)]) {
            .static_assert,
            .typedef,
            .struct_decl_two,
            .union_decl_two,
            .enum_decl_two,
            .struct_decl,
            .union_decl,
            .enum_decl,
            => {},

            .fn_proto,
            .static_fn_proto,
            .inline_fn_proto,
            .inline_static_fn_proto,
            .extern_var,
            .threadlocal_extern_var,
            => {
                const decl_data = codegen.node_data[@intFromEnum(decl)].decl;
                const name = codegen.tree.tokSlice(decl_data.name);
                const name_id = try codegen.comp.internString(name);
                try codegen.scope.addSymbol(codegen.comp.gpa, name_id, decl);
            },

            .fn_def,
            .inline_fn_def,
            => try codegen.genFn(decl, false),

            .static_fn_def,
            .inline_static_fn_def,
            => try codegen.genFn(decl, true),

            .@"var",
            .static_var,
            .threadlocal_var,
            .threadlocal_static_var,
            => try codegen.genVar(decl),

            else => unreachable,
        }
    }
    try codegen.text.writeAll("  .section  .note.GNU-stack,\"\",@progbits\n");
    const text_slice = try text.toOwnedSlice(tree.comp.gpa);
    errdefer tree.comp.gpa.free(text_slice);
    const data_slice = try data.toOwnedSlice(tree.comp.gpa);
    return .{
        .text = text_slice,
        .data = data_slice,
    };
}

// fn callingConvention(c: *AsmCodeGen, params_or_args: CallConv.ParamsOrArgs, gp_count: *i32, fp_count: *i32) !i32 {
//     var stack: i32 = 0;
//     var gp = gp_count.*;
//     var fp: i32 = 0;
//     std.debug.assert(c.call_conv.items.len == 0);
//     try c.call_conv.appendNTimes(c.comp.gpa, .default, params_or_args.len());
//     var it = params_or_args.iterator(c);
//     var i: usize = 0;
//     while (it.next()) |ty| : (i += 1) {
//         switch (ty.specifier) {
//             .@"struct",
//             .@"union",
//             => return c.todoTok("record params for functions", 0),
//             .float, .double => {
//                 defer fp += 1;
//                 if (fp < FP_MAX) continue;
//             },
//             .long_double => {},
//             else => {
//                 defer gp += 1;
//                 if (gp < GP_MAX) continue;
//             },
//         }
//         c.call_conv.items[i].pass_by_stack = true;
//         const param_align = ty.alignof(c.comp);
//         if (param_align > 8) {
//             stack = std.mem.alignForward(i32, stack, param_align);
//         }
//         c.call_conv.items[i].stack_offset = stack;
//         stack += std.mem.alignForward(i32, @intCast(ty.sizeof(c.comp).?), 8);
//     }
//     gp_count.* = @min(gp, GP_MAX);
//     fp_count.* = @min(fp, FP_MAX);
//     return stack;
// }

fn genFn(c: *AsmCodeGen, node: NodeIndex, is_static: bool) !void {
    const fn_ty = c.node_ty[@intFromEnum(node)];
    const decl = c.node_data[@intFromEnum(node)].decl;
    const name = c.tree.tokSlice(decl.name);
    const name_id = try c.comp.internString(name);
    const params = fn_ty.params();
    try c.scope.addSymbol(c.comp.gpa, name_id, node);
    std.debug.assert(c.current_fn_params.count() == 0);

    try c.current_fn_params.ensureTotalCapacity(c.comp.gpa, params.len);
    defer c.current_fn_params.clearRetainingCapacity();

    for (params) |param| {
        c.current_fn_params.putAssumeCapacity(param.name, 0);
    }

    try c.text.print("  .{s} \"{s}\"\n", .{ if (is_static) "local" else "globl", name });

    if (c.comp.code_gen_options.func_sections) {
        try c.text.print("  .section .text.\"{s}\",\"ax\",@progbits\n", .{name});
    } else {
        try c.text.writeAll("  .text\n");
    }
    try c.text.print(
        \\  .type "{0s}", @function
        \\"{0s}":
        \\
    , .{name});

    std.debug.assert(c.call_conv.items.len == 0);
    defer c.call_conv.items.len = 0;

    const return_by_stack = (fn_ty.returnType().sizeof(c.comp) orelse 0) > 16;
    const params_or_args: CallConv.ParamsOrArgs = .{ .params = params };
    try c.call_conv.ensureUnusedCapacity(c.comp.gpa, params.len);
    const call_conv = try CallConv.compute(params_or_args.iterator(&.{}), return_by_stack, c.comp, c.call_conv.unusedCapacitySlice());
    c.call_conv.items.len += params.len;

    const gp_count = call_conv.gp_count;
    const fp_count = call_conv.fp_count;
    // c.current_fn = fn;

    // Prologue
    try c.text.writeAll(
        \\  push %rbp
        \\  mov %rsp, %rbp
        \\
    );
    const old_writer = c.text;

    var this_fn: std.ArrayListUnmanaged(u8) = .empty;
    defer this_fn.deinit(c.tree.comp.gpa);

    c.text = this_fn.writer(c.tree.comp.gpa);

    c.lvar_stk_sz = 0;
    // Save arg registers if function is variadic
    if (fn_ty.is(.var_args_func)) {
        c.va_gp_start = gp_count * 8;
        c.va_fp_start = fp_count * 16 + 48;
        c.va_st_start = call_conv.stack + 16;
        c.lvar_stk_sz += 176;

        if (gp_count <= 0) try c.text.writeAll("  movq %rdi, -176(%rbp)\n");
        if (gp_count <= 1) try c.text.writeAll("  movq %rsi, -168(%rbp)\n");
        if (gp_count <= 2) try c.text.writeAll("  movq %rdx, -160(%rbp)\n");
        if (gp_count <= 3) try c.text.writeAll("  movq %rcx, -152(%rbp)\n");
        if (gp_count <= 4) try c.text.writeAll("  movq %r8, -144(%rbp)\n");
        if (gp_count <= 5) try c.text.writeAll("  movq %r9, -136(%rbp)\n");
        if (fp_count > 8) {
            try c.text.writeAll(
                \\  test %al, %al
                \\  je 1f
                \\
            );
            if (fp_count <= 0) try c.text.writeAll("  movaps %xmm0, -128(%rbp)\n");
            if (fp_count <= 1) try c.text.writeAll("  movaps %xmm1, -112(%rbp)\n");
            if (fp_count <= 2) try c.text.writeAll("  movaps %xmm2, -96(%rbp)\n");
            if (fp_count <= 3) try c.text.writeAll("  movaps %xmm3, -80(%rbp)\n");
            if (fp_count <= 4) try c.text.writeAll("  movaps %xmm4, -64(%rbp)\n");
            if (fp_count <= 5) try c.text.writeAll("  movaps %xmm5, -48(%rbp)\n");
            if (fp_count <= 6) try c.text.writeAll("  movaps %xmm6, -32(%rbp)\n");
            if (fp_count <= 7) try c.text.writeAll("  movaps %xmm7, -16(%rbp)\n");
            try c.text.writeAll("1:\n");
        }
    }
    // TODO: dealloc vla

    if (return_by_stack) {
        c.lvar_stk_sz += 8;
        c.rtn_ptr_ofs = c.lvar_stk_sz;
        try c.text.print("  mov {s}, -{d}(%rbp)\n", .{ argreg64[0], c.rtn_ptr_ofs });
    }

    // TODO: put args into scope

    c.lvar_stk_sz = try c.assignLvarOffsets(c.tree.childNodes(decl.node), c.lvar_stk_sz, false);
    c.lvar_stk_sz = std.mem.alignForward(i32, c.lvar_stk_sz, 8);
    c.peak_stk_usage = c.lvar_stk_sz;

    // TODO: Save passed-by-register arguments to the stack

    try c.genStmt(decl.node);
    std.debug.assert(c.tmp_stk.items.len == 0);

    c.text = old_writer;
    try c.text.print("  sub ${d}, %rsp\n", .{std.mem.alignForward(i32, c.peak_stk_usage, 16)});
    try c.text.writeAll(this_fn.items);

    // Epilogue
    try c.text.writeAll(
        \\9:
        \\  mov %rbp, %rsp
        \\  pop %rbp
        \\  ret
        \\
    );
}

fn pushTmpstack(c: *AsmCodeGen, sz: i32) !i32 {
    try c.tmp_stk.ensureUnusedCapacity(c.comp.gpa, 1);
    var offset: i32 = undefined;
    if (c.dont_reuse_stack) {
        c.peak_stk_usage += 8 * sz;
        offset = c.peak_stk_usage;
    } else {
        var stk_pos: i32 = if (c.tmp_stk.items.len > 0) c.tmp_stk.items[@intCast(c.tmp_stk.items.len - 1)] else c.lvar_stk_sz;
        stk_pos += 8 * sz;
        c.peak_stk_usage = @max(c.peak_stk_usage, stk_pos);
        offset = stk_pos;
    }
    c.tmp_stk.appendAssumeCapacity(offset);
    return offset;
}

fn push(c: *AsmCodeGen) !i32 {
    const offset = try c.pushTmpstack(1);
    try c.text.print("  mov %rax, -{d}(%rbp)\n", .{offset});
    return offset;
}

fn genCall(c: *AsmCodeGen, call: NodeIndex) Error!void {
    const child_nodes = c.tree.childNodes(call);
    const func = child_nodes[0];
    const fn_ptr = c.node_ty[@intFromEnum(func)];
    const fn_ty = fn_ptr.elemType();
    const args = child_nodes[1..];
    // Evaluate function pointer
    try c.genExpr(func);
    _ = try c.push();

    // Evaluate arguments
    for (args) |arg| {
        try c.genAddr(arg);
        _ = try c.push();
        try c.genExpr(arg);
        try c.store(c.node_ty[@intFromEnum(arg)], arg);
    }
    try c.pop("%r10");

    const return_by_stack = false; // TODO: handle large record return value

    const params_or_args: CallConv.ParamsOrArgs = .{ .args = args };
    try c.call_conv.ensureUnusedCapacity(c.comp.gpa, args.len);
    const old_cc_len = c.call_conv.items.len;
    defer c.call_conv.items.len = old_cc_len;
    const call_conv = try CallConv.compute(params_or_args.iterator(c.node_ty), return_by_stack, c.comp, c.call_conv.unusedCapacitySlice());
    c.call_conv.items.len += args.len;

    try c.text.print("  sub ${d}, %rsp\n", .{std.mem.alignForward(u32, call_conv.stack, 16)});

    try c.placeStackArgs(old_cc_len, args);
    try c.placeRegArgs(old_cc_len, args, return_by_stack, call);

    if (fn_ty.is(.var_args_func)) {
        try c.text.print("  movl ${d}, %eax\n", .{call_conv.fp_count});
    }
    try c.text.print(
        \\  call *%r10
        \\  add ${d}, %rsp
        \\
    , .{std.mem.alignForward(u32, call_conv.stack, 16)});

    // It looks like the most significant 48 or 56 bits in RAX may
    // contain garbage if a function return type is short or bool/char,
    // respectively. We clear the upper bits here.
    const ret_ty = fn_ty.returnType();
    if (ret_ty.isInt() and ret_ty.sizeof(c.comp).? < 4) {
        if (ret_ty.is(.bool)) {
            try c.cast(Type.int, .{ .specifier = .uchar });
        } else {
            try c.cast(Type.int, ret_ty);
        }
    }

    // TODO: small struct return in registers
}

fn genStmt(c: *AsmCodeGen, stmt: NodeIndex) !void {
    const tag = c.node_tag[@intFromEnum(stmt)];
    switch (tag) {
        .compound_stmt_two,
        .compound_stmt,
        => {
            try c.scope.push(c.comp.gpa);
            defer c.scope.pop();
            const child_nodes = c.tree.childNodes(stmt);
            for (child_nodes) |node| {
                try c.genStmt(node);
            }
        },
        .call_expr_one, .call_expr => return c.genCall(stmt),
        .return_stmt => {
            const value_node = c.node_data[@intFromEnum(stmt)].un;
            if (value_node != .none) {
                try c.genExpr(value_node);
                const ret_expr_ty = c.node_ty[@intFromEnum(value_node)];
                if (ret_expr_ty.isRecord()) {
                    return c.todoNode("Return record by value", value_node);
                }
            }
            try c.text.writeAll("  jmp 9f\n");
        },
        .assign_expr => {
            const bin = c.node_data[@intFromEnum(stmt)].bin;
            try c.genAddr(bin.lhs);
            _ = try c.push();
            try c.genExpr(bin.rhs);

            if (c.tree.isBitfield(bin.lhs)) {
                return c.todoNode("assign to bitfield", bin.lhs);
            }

            try c.store(c.node_ty[@intFromEnum(stmt)], stmt);
        },
        .@"var",
        .extern_var,
        .static_var,
        .implicit_static_var,
        .threadlocal_var,
        .threadlocal_extern_var,
        .threadlocal_static_var,
        => {
            const decl = c.node_data[@intFromEnum(stmt)].decl;
            if (decl.node != .none) {
                return c.todoNode("variable initializer", decl.node);
            }
            const name = c.tree.tokSlice(decl.name);
            const name_id = try c.comp.internString(name);
            try c.scope.addSymbol(c.comp.gpa, name_id, stmt);
            // TODO: initializer
        },
        inline else => |t| {
            return c.todoNode("genStmt for " ++ @tagName(t), stmt);
        },
    }
}

fn popTmpstack(c: *AsmCodeGen) i32 {
    return c.tmp_stk.pop();
}

fn pop(c: *AsmCodeGen, arg: []const u8) !void {
    const offset = c.popTmpstack();
    return c.text.print("  mov -{d}(%rbp), {s}\n", .{ offset, arg });
}

fn cmpZero(c: *AsmCodeGen, ty: Type) !void {
    switch (ty.specifier) {
        .float => return c.text.writeAll(
            \\  xorps %xmm1, %xmm1
            \\  ucomiss %xmm1, %xmm0
            \\
        ),
        .double => return c.text.writeAll(
            \\  xorpd %xmm1, %xmm1
            \\  ucomisd %xmm1, %xmm0
            \\
        ),
        .long_double => return c.text.writeAll(
            \\  fldz
            \\  fucomip
            \\  fstp %st(0)
            \\
        ),
        else => {},
    }
    if (ty.isInt() and ty.sizeof(c.comp).? <= 4) {
        return c.text.writeAll("  test %eax, %eax\n");
    }
    return c.text.writeAll("  test %rax, %rax\n");
}

fn getTypeId(c: *AsmCodeGen, ty: Type) TypeId {
    return switch (ty.specifier) {
        .char => if (ty.isUnsignedInt(c.comp)) .u8 else .i8,
        .schar => .i8,
        .uchar => .u8,
        .short => .i16,
        .ushort => .u16,
        .int => .i32,
        .uint => .u32,
        .long, .long_long => .i64,
        .ulong, .ulong_long => .u64,
        .float => .f32,
        .double => .f64,
        .long_double => .f80,
        else => .u64,
    };
}

const TypeId = enum {
    i8,
    i16,
    i32,
    i64,
    u8,
    u16,
    u32,
    u64,
    f32,
    f64,
    f80,
};

fn cast(c: *AsmCodeGen, from: Type, to: Type) !void {
    if (to.is(.void)) return;
    if (to.is(.bool)) {
        try c.cmpZero(from);
        return c.text.writeAll(
            \\  setne %al
            \\  movzx %al, %eax
            \\
        );
    }
    const t1 = c.getTypeId(from);
    const t2 = c.getTypeId(to);
    if (cast_table[@intFromEnum(t1)][@intFromEnum(t2)]) |instr| {
        try c.text.writeAll("  ");
        try c.text.writeAll(instr);
        return c.text.writeByte('\n');
    }
}

fn genAddr(c: *AsmCodeGen, node: NodeIndex) !void {
    const ty = c.node_ty[@intFromEnum(node)];

    if (ty.is(.variable_len_array)) {
        return c.todoNode("genAddr VLA", node);
    }
    if (c.ofs.get(node)) |offset| {
        return c.text.print("  lea {d}(%rbp), %rax\n", .{offset});
    }

    var name: ?[]const u8 = null;

    const actual_node = if (c.node_tag[@intFromEnum(node)] == .decl_ref_expr) blk: {
        const decl_ref = c.node_data[@intFromEnum(node)].decl_ref;
        name = c.tree.tokSlice(decl_ref);
        const name_id = try c.comp.internString(name.?);
        break :blk c.scope.getDeclNode(name_id);
    } else node;

    const is_pic = switch (c.comp.code_gen_options.pic_level) {
        .one, .two => true,
        .none => false,
    };
    const decl_tag = c.node_tag[@intFromEnum(actual_node)];
    const is_threadlocal = switch (decl_tag) {
        .threadlocal_var,
        .threadlocal_extern_var,
        .threadlocal_static_var,
        => true,
        else => false,
    };
    if (is_pic) {
        if (is_threadlocal) {
            return c.text.print(
                \\  data16 lea "{s}"@tlsgd(%rip), %rdi
                \\  .value 0x6666
                \\  rex64
                \\  call __tls_get_addr@PLT
                \\
            , .{name.?});
        }
        return c.text.print("  mov \"{s}\"@GOTPCREL(%rip), %rax\n", .{name.?});
    }
    if (is_threadlocal) {
        return c.text.print(
            \\  mov %fs:0, %rax
            \\  add $"{s}"@tpoff, %rax
            \\
        , .{name.?});
    }
    if (ty.isFunc()) {
        const is_def = switch (decl_tag) {
            .fn_def,
            .static_fn_def,
            .inline_fn_def,
            .inline_static_fn_def,
            => true,
            .fn_proto,
            .static_fn_proto,
            .inline_fn_proto,
            .inline_static_fn_proto,
            => false,
            else => unreachable,
        };
        if (is_def) {
            return c.text.print("  lea \"{s}\"(%rip), %rax\n", .{name.?});
        }
        return c.text.print("  mov \"{s}\"@GOTPCREL(%rip), %rax\n", .{name.?});
    }
    return c.text.print("  lea \"{s}\"(%rip), %rax\n", .{name.?});
}

fn regopAx(c: *AsmCodeGen, ty: Type, node: NodeIndex) ![]const u8 {
    const size = ty.sizeof(c.comp).?;
    return switch (size) {
        1, 2, 4 => "%eax",
        8 => "%rax",
        16 => c.todoNode("__int128", node),
        else => c.todoNode("_BitInt", node),
    };
}

/// When we load a char or a short value to a register, we always
/// extend them to the size of int, so we can assume the lower half of
/// a register always contains a valid value.
fn loadExtendInt(c: *AsmCodeGen, ty: Type, offset: i32, ptr: []const u8, reg: []const u8, node: NodeIndex) !void {
    const instruction = if (ty.isUnsignedInt(c.comp)) "movz" else "movs";
    const size = ty.sizeof(c.comp).?;
    switch (size) {
        1 => try c.text.print("  {s}bl {d}({s}), {s}\n", .{ instruction, offset, ptr, reg }),
        2 => try c.text.print("  {s}wl {d}({s}), {s}\n", .{ instruction, offset, ptr, reg }),
        4 => try c.text.print("  movl {d}({s}), {s}\n", .{ offset, ptr, reg }),
        8 => try c.text.print("  mov {d}({s}), {s}\n", .{ offset, ptr, reg }),
        16 => return c.todoNode("__int128", node),
        else => return c.todoNode("_BitInt", node),
    }
}

fn load(c: *AsmCodeGen, ty: Type, node: NodeIndex) !void {
    switch (ty.specifier) {
        .@"struct",
        .@"union",
        .func,
        .var_args_func,
        .old_style_func,
        .array,
        .static_array,
        .incomplete_array,
        .vector,
        .variable_len_array,
        => {},
        .float => return c.text.writeAll("  movss (%rax), %xmm0\n"),
        .double => return c.text.writeAll("  movsd (%rax), %xmm0\n"),
        .long_double => return c.text.writeAll("  fninit; fldt (%rax)\n"),
        else => {
            std.debug.assert(ty.isInt());
            try c.loadExtendInt(ty, 0, "%rax", try c.regopAx(ty, node), node);
        },
    }
}

fn store(c: *AsmCodeGen, ty: Type, node: NodeIndex) !void {
    try c.pop("%rcx");
    switch (ty.specifier) {
        .@"struct",
        .@"union",
        => return c.todoNode("store struct/union", node),
        .float => return c.text.writeAll("  movss %xmm0, (%rcx)\n"),
        .double => return c.text.writeAll("  movsd %xmm0, (%rcx)\n"),
        .long_double => return c.text.writeAll(
            \\  fstpt (%rcx)
            \\  fninit; fldt (%rcx)
            \\
        ),
        else => {},
    }
    switch (ty.sizeof(c.comp).?) {
        1 => return c.text.writeAll("  mov %al, (%rcx)\n"),
        2 => return c.text.writeAll("  mov %ax, (%rcx)\n"),
        4 => return c.text.writeAll("  mov %eax, (%rcx)\n"),
        8 => return c.text.writeAll("  mov %rax, (%rcx)\n"),
        16 => return c.todoNode("store __int128", node),
        else => return c.todoNode("store _BitInt", node),
    }
}

fn genExpr(c: *AsmCodeGen, expr: NodeIndex) !void {
    const tag = c.node_tag[@intFromEnum(expr)];
    switch (tag) {
        .int_literal => {
            const ty = c.node_ty[@intFromEnum(expr)];
            const value = c.tree.value_map.get(expr).?;
            try c.text.writeAll("  mov $");
            _ = try value.print(ty, c.comp, c.text);
            try c.text.writeAll(", %rax\n");
        },
        .implicit_cast, .explicit_cast => {
            const operand = c.node_data[@intFromEnum(expr)].cast.operand;
            try c.genExpr(operand);
            try c.cast(c.node_ty[@intFromEnum(operand)], c.node_ty[@intFromEnum(expr)]);
        },
        .decl_ref_expr => {
            try c.genAddr(expr);
            try c.load(c.node_ty[@intFromEnum(expr)].canonicalize(.standard), expr);
        },
        .string_literal_expr => {
            const unique_id = try c.emitStringLiteral(expr);
            return c.text.print("  lea \".L..{d}\"(%rip), %rax\n", .{unique_id});
        },
        inline else => |t| {
            return c.todoNode("genExpr for " ++ @tagName(t), expr);
        },
    }
}

fn getUniqueId(c: *AsmCodeGen) u32 {
    defer c.count += 1;
    return c.count;
}

fn emitStringLiteral(c: *AsmCodeGen, expr: NodeIndex) !u32 {
    std.debug.assert(c.node_tag[@intFromEnum(expr)] == .string_literal_expr);

    const unique_id = c.getUniqueId();
    const ty = c.node_ty[@intFromEnum(expr)];
    const size = ty.sizeof(c.comp).?;
    const alignment = ty.alignof(c.comp);
    try c.data.print(
        \\  .local ".L..{0d}"
        \\  .data
        \\  .type ".L..{0d}", @object
        \\  .size ".L..{0d}", {1d}
        \\  .align {2d}
        \\".L..{0d}":
        \\
    , .{ unique_id, size, alignment });

    try c.emitValue(ty, expr);
    return unique_id;
}

fn assignLvarOffsets(c: *AsmCodeGen, nodes: []const NodeIndex, bot: i32, in_call_expr: bool) !i32 {
    var bottom = bot;
    // todo: stack align params

    for (nodes) |child| {
        const tag = c.node_tag[@intFromEnum(child)];
        const node_is_var = switch (tag) {
            .@"var",
            .extern_var,
            .static_var,
            .implicit_static_var,
            .threadlocal_var,
            .threadlocal_extern_var,
            .threadlocal_static_var,
            => true,
            else => false,
        };
        if (node_is_var or in_call_expr) {
            const ty = c.node_ty[@intFromEnum(child)];
            const size = ty.sizeof(c.comp).?;
            const alignment = if (ty.isArray() and size >= 16) @max(16, ty.alignof(c.comp)) else ty.alignof(c.comp);

            bottom += @intCast(size);
            bottom = std.mem.alignForward(i32, bottom, alignment);
            try c.ofs.put(c.comp.gpa, child, -bottom);
        }
    }

    var max_depth = bottom;
    for (nodes) |child| {
        const tag = c.node_tag[@intFromEnum(child)];
        switch (tag) {
            .compound_stmt_two,
            .array_init_expr_two,
            .struct_init_expr_two,
            .call_expr_one,
            .generic_expr_one,
            .compound_stmt,
            .array_init_expr,
            .struct_init_expr,
            .call_expr,
            .generic_expr,
            => {
                const is_call_expr = tag == .call_expr or tag == .call_expr_one;
                const child_nodes = c.tree.childNodes(child);

                const sub_depth = try c.assignLvarOffsets(if (is_call_expr) child_nodes[1..] else child_nodes, bottom, is_call_expr);
                if (c.dont_reuse_stack) {
                    max_depth = sub_depth;
                    bottom = max_depth;
                } else {
                    max_depth = @max(max_depth, sub_depth);
                }
            },
            else => continue,
        }
    }
    return max_depth;
}

fn placeStackArgs(c: *AsmCodeGen, cc_start: usize, args: []const NodeIndex) !void {
    const call_conv = c.call_conv.items[cc_start..args.len];
    for (args, call_conv) |arg, cc| {
        if (!cc.pass_by_stack) continue;

        const ty = c.node_ty[@intFromEnum(arg)].canonicalize(.standard);
        switch (ty.specifier) {
            .@"struct",
            .@"union",
            .float,
            .double,
            .long_double,
            => return c.todoNode("memcopy stack arg", arg),
            else => {
                try c.loadExtendInt(ty, c.ofs.get(arg).?, "%rbp", try c.regopAx(ty, arg), arg);
                try c.text.print("  mov %rax, {d}(%rsp)\n", .{cc.stack_offset});
            },
        }
    }
}

fn placeRegArgs(c: *AsmCodeGen, cc_start: usize, args: []const NodeIndex, return_by_stack: bool, call_node: NodeIndex) !void {
    var gp: i32 = 0;
    var fp: i32 = 0;
    if (return_by_stack) {
        return c.todoNode("Return by stack", call_node);
    }
    const call_conv = c.call_conv.items[cc_start..args.len];
    for (args, call_conv) |arg, cc| {
        if (cc.pass_by_stack) continue;
        const ty = c.node_ty[@intFromEnum(arg)].canonicalize(.standard);
        switch (ty.specifier) {
            .@"struct",
            .@"union",
            => return c.todoNode("pass struct or union in register", arg),
            .float => {
                defer fp += 1;
                try c.text.print("  movss {d}(%rbp), %xmm{d}", .{ 0, fp });
            },
            .double => {
                defer fp += 1;
                try c.text.print("  movsd {d}(%rbp), %xmm{d}", .{ 0, fp });
            },
            else => {
                defer gp += 1;
                const size = ty.sizeof(c.comp).?;
                const argreg = if (size <= 4) argreg32[@intCast(gp)] else argreg64[@intCast(gp)];
                try c.loadExtendInt(ty, c.ofs.get(arg).?, "%rbp", argreg, arg);
            },
        }
    }
}

fn genVar(c: *AsmCodeGen, node: NodeIndex) !void {
    const comp = c.comp;
    const ty = c.node_ty[@intFromEnum(node)];
    const tag = c.node_tag[@intFromEnum(node)];
    const decl_data = c.node_data[@intFromEnum(node)].decl;

    const is_threadlocal = tag == .threadlocal_var or tag == .threadlocal_static_var;
    const is_static = tag == .static_var or tag == .threadlocal_static_var;
    const is_tentative = decl_data.node == .none;
    const size = ty.sizeof(comp) orelse blk: {
        // tentative array definition assumed to have one element
        std.debug.assert(is_tentative and ty.isArray());
        break :blk ty.elemType().sizeof(comp).?;
    };

    const name = c.tree.tokSlice(decl_data.name);
    const name_id = try c.comp.internString(name);
    try c.scope.addSymbol(c.comp.gpa, name_id, node);
    const nat_align = ty.alignof(comp);
    const alignment = if (ty.isArray() and size >= 16) @max(16, nat_align) else nat_align;

    if (is_static) {
        try c.data.print("  .local \"{s}\"\n", .{name});
    } else {
        try c.data.print("  .globl \"{s}\"\n", .{name});
    }

    if (is_tentative and comp.code_gen_options.common) {
        return c.data.print("  .comm \"{s}\", {d}, {d}\n", .{ name, size, alignment });
    }
    if (!is_tentative) {
        if (is_threadlocal and comp.code_gen_options.data_sections) {
            try c.data.print("  .section .tdata.\"{s}\",\"awT\",@progbits\n", .{name});
        } else if (is_threadlocal) {
            try c.data.writeAll("  .section .tdata,\"awT\",@progbits\n");
        } else if (comp.code_gen_options.data_sections) {
            try c.data.print("  .section .data.\"{s}\",\"aw\",@progbits\n", .{name});
        } else {
            try c.data.writeAll("  .data\n");
        }
        try c.data.print(
            \\  .type "{0s}", @object
            \\  .size "{0s}", {1d}
            \\  .align {2d}
            \\  "{0s}":
            \\
        , .{ name, size, alignment });
        return c.emitValue(ty, decl_data.node);
    }
    if (is_threadlocal and comp.code_gen_options.data_sections) {
        try c.data.print("  .section .tbss.\"{s}\",\"awT\",@nobits\n", .{name});
    } else if (is_threadlocal) {
        try c.data.writeAll("  .section .tbss,\"awT\",@nobits\n");
    } else if (comp.code_gen_options.data_sections) {
        try c.data.print("  .section .bss.\"{s}\",\"aw\",@nobits\n", .{name});
    } else {
        try c.data.writeAll("  .bss\n");
    }
    try c.data.print(
        \\  .align {d}
        \\  "{s}"
        \\  .zero {d}
        \\
    , .{ alignment, name, size });
}
