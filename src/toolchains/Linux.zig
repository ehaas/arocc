const std = @import("std");
const mem = std.mem;
const Compilation = @import("../Compilation.zig");
const GCCDetector = @import("GCCDetector.zig");
const Toolchain = @import("../Toolchain.zig");
const Driver = @import("../Driver.zig");
const Distro = @import("../Distro.zig");
const target_util = @import("../target.zig");
const system_defaults = @import("system_defaults");

const Linux = @This();

distro: Distro.Tag = .unknown,
extra_opts: std.ArrayListUnmanaged([]const u8) = .{},
gcc_detector: GCCDetector = .{},

pub fn discover(self: *Linux, tc: *Toolchain) !void {
    self.distro = Distro.detect(tc.getTarget());
    try self.gcc_detector.discover(tc);
    tc.selected_multilib = self.gcc_detector.selected;

    try self.gcc_detector.appendToolPath(tc);
    try self.buildExtraOpts(tc);
    try self.findPaths(tc);
}

fn buildExtraOpts(self: *Linux, tc: *const Toolchain) !void {
    const gpa = tc.driver.comp.gpa;
    const target = tc.getTarget();
    const is_android = target.isAndroid();
    if (self.distro.isAlpine() or is_android) {
        try self.extra_opts.ensureUnusedCapacity(gpa, 2);
        self.extra_opts.appendAssumeCapacity("-z");
        self.extra_opts.appendAssumeCapacity("now");
    }

    if (self.distro.isOpenSUSE() or self.distro.isUbuntu() or self.distro.isAlpine() or is_android) {
        try self.extra_opts.ensureUnusedCapacity(gpa, 2);
        self.extra_opts.appendAssumeCapacity("-z");
        self.extra_opts.appendAssumeCapacity("relro");
    }

    if (target.cpu.arch.isARM() or target.cpu.arch.isAARCH64() or is_android) {
        try self.extra_opts.ensureUnusedCapacity(gpa, 2);
        self.extra_opts.appendAssumeCapacity("-z");
        self.extra_opts.appendAssumeCapacity("max-page-size=4096");
    }

    if (target.cpu.arch == .arm or target.cpu.arch == .thumb) {
        try self.extra_opts.append(gpa, "-X");
    }

    if (!target.cpu.arch.isMIPS() and target.cpu.arch != .hexagon) {
        const hash_style = if (is_android) .both else self.distro.getHashStyle();
        try self.extra_opts.append(gpa, switch (hash_style) {
            inline else => |tag| "--hash-style=" ++ @tagName(tag),
        });
    }

    if (system_defaults.enable_linker_build_id) {
        try self.extra_opts.append(gpa, "--build-id");
    }
}

fn addMultiLibPaths(self: *Linux, tc: *Toolchain, sysroot: []const u8, os_lib_dir: []const u8) !void {
    if (!self.gcc_detector.is_valid) return;
    const gcc_triple = self.gcc_detector.gcc_triple;
    const lib_path = self.gcc_detector.parent_lib_path;

    // Add lib/gcc/$triple/$version, with an optional /multilib suffix.
    try tc.addPathIfExists(&.{ self.gcc_detector.install_path, tc.selected_multilib.gcc_suffix }, .file);

    // Add lib/gcc/$triple/$libdir
    // For GCC built with --enable-version-specific-runtime-libs.
    try tc.addPathIfExists(&.{ self.gcc_detector.install_path, "..", os_lib_dir }, .file);

    try tc.addPathIfExists(&.{ lib_path, "..", gcc_triple, "lib", "..", os_lib_dir, tc.selected_multilib.os_suffix }, .file);

    // If the GCC installation we found is inside of the sysroot, we want to
    // prefer libraries installed in the parent prefix of the GCC installation.
    // It is important to *not* use these paths when the GCC installation is
    // outside of the system root as that can pick up unintended libraries.
    // This usually happens when there is an external cross compiler on the
    // host system, and a more minimal sysroot available that is the target of
    // the cross. Note that GCC does include some of these directories in some
    // configurations but this seems somewhere between questionable and simply
    // a bug.
    if (mem.startsWith(u8, lib_path, sysroot)) {
        try tc.addPathIfExists(&.{ lib_path, "..", os_lib_dir }, .file);
    }
}

fn addMultiArchPaths(self: *Linux, tc: *Toolchain) !void {
    if (!self.gcc_detector.is_valid) return;
    const lib_path = self.gcc_detector.parent_lib_path;
    const gcc_triple = self.gcc_detector.gcc_triple;
    const multilib = self.gcc_detector.selected;
    try tc.addPathIfExists(&.{ lib_path, "..", gcc_triple, "lib", multilib.os_suffix }, .file);
}

/// TODO: Very incomplete
fn findPaths(self: *Linux, tc: *Toolchain) !void {
    const target = tc.getTarget();
    const sysroot = tc.getSysroot();

    const os_lib_dir = getOSLibDir(target);
    const multiarch_triple = getMultiarchTriple(target);

    try self.addMultiLibPaths(tc, sysroot, os_lib_dir);

    try tc.addPathIfExists(&.{ sysroot, "/lib", multiarch_triple }, .file);
    try tc.addPathIfExists(&.{ sysroot, "/lib", "..", os_lib_dir }, .file);

    if (target.isAndroid()) {
        // TODO
    }
    try tc.addPathIfExists(&.{ sysroot, "/usr", "lib", multiarch_triple }, .file);
    try tc.addPathIfExists(&.{ sysroot, "/usr", "lib", "..", os_lib_dir }, .file);

    try self.addMultiArchPaths(tc);

    try tc.addPathIfExists(&.{ sysroot, "/lib" }, .file);
    try tc.addPathIfExists(&.{ sysroot, "/usr", "lib" }, .file);
}

pub fn deinit(self: *Linux, allocator: std.mem.Allocator) void {
    self.extra_opts.deinit(allocator);
}

fn isPIEDefault(self: *const Linux) bool {
    _ = self;
    return false;
}

fn getPIE(self: *const Linux, d: *const Driver) bool {
    if (d.shared or d.static or d.relocatable or d.static_pie) {
        return false;
    }
    return d.pie orelse self.isPIEDefault();
}

fn getStaticPIE(self: *const Linux, d: *Driver) !bool {
    _ = self;
    if (d.static_pie and d.pie != null) {
        try d.err("cannot specify 'nopie' along with 'static-pie'");
    }
    return d.static_pie;
}

fn getStatic(self: *const Linux, d: *const Driver) bool {
    _ = self;
    return d.static and !d.static_pie;
}

pub fn getDefaultLinker(self: *const Linux, target: std.Target) []const u8 {
    _ = self;
    if (target.isAndroid()) {
        return "ld.lld";
    }
    return "ld";
}

pub fn buildLinkerArgs(self: *const Linux, tc: *const Toolchain, argv: *std.ArrayList([]const u8)) Compilation.Error!void {
    const d = tc.driver;

    const is_pie = self.getPIE(d);
    const is_static_pie = try self.getStaticPIE(d);
    const is_static = self.getStatic(d);
    const is_android = d.comp.target.isAndroid();
    const is_iamcu = d.comp.target.os.tag == .elfiamcu;

    if (is_pie) {
        try argv.append("-pie");
    }
    if (is_static_pie) {
        try argv.ensureUnusedCapacity(5);
        argv.appendAssumeCapacity("-static");
        argv.appendAssumeCapacity("-pie");
        argv.appendAssumeCapacity("--no-dynamic-linker");
        argv.appendAssumeCapacity("-z");
        argv.appendAssumeCapacity("text");
    }

    if (d.rdynamic) {
        try argv.append("-export-dynamic");
    }

    if (d.strip) {
        try argv.append("-s");
    }

    try argv.ensureUnusedCapacity(self.extra_opts.items.len);
    argv.appendSliceAssumeCapacity(self.extra_opts.items);

    try argv.append("--eh-frame-hdr");

    // Todo: Driver should parse `-EL`/`-EB` for arm to set endianness for arm targets
    if (target_util.ldEmulationOption(d.comp.target, null)) |emulation| {
        try argv.ensureUnusedCapacity(2);
        argv.appendAssumeCapacity("-m");
        argv.appendAssumeCapacity(emulation);
    } else {
        try d.err("Unknown target triple");
        return;
    }
    if (d.comp.target.cpu.arch.isRISCV()) {
        try argv.append("-X");
    }
    if (d.shared) {
        try argv.append("-shared");
    }
    if (is_static) {
        try argv.append("-static");
    } else {
        if (d.rdynamic) {
            try argv.append("-export-dynamic");
        }
        if (!d.shared and !is_static_pie and !d.relocatable) {
            const dynamic_linker = d.comp.target.standardDynamicLinkerPath();
            // todo: check for --dyld-prefix
            if (dynamic_linker.get()) |path| {
                try argv.ensureUnusedCapacity(2);
                argv.appendAssumeCapacity("-dynamic-linker");
                argv.appendAssumeCapacity(try tc.arena.dupe(u8, path));
            } else {
                try d.err("Could not find dynamic linker path");
            }
        }
    }

    try argv.ensureUnusedCapacity(2);
    argv.appendAssumeCapacity("-o");
    argv.appendAssumeCapacity(d.output_name orelse "a.out");

    if (!d.nostdlib and !d.nostartfiles and !d.relocatable) {
        if (!is_android and !is_iamcu) {
            if (!d.shared) {
                const crt1 = if (is_pie)
                    "Scrt1.o"
                else if (is_static_pie)
                    "rcrt1.o"
                else
                    "crt1.o";
                try argv.append(try tc.getFilePath(crt1));
            }
            try argv.append(try tc.getFilePath("crti.o"));
        }
    }

    // TODO add -L opts
    // TODO add -u opts

    try tc.addFilePathLibArgs(argv);

    // TODO handle LTO

    try argv.appendSlice(d.link_objects.items);

    if (!d.nostdlib and !d.relocatable) {
        if (!d.nodefaultlibs) {
            if (is_static or is_static_pie) {
                try argv.append("--start-group");
            }
            // TODO: add pthread if needed
            if (!d.nolibc) {
                try argv.append("-lc");
            }
            if (is_iamcu) {
                try argv.append("-lgloss");
            }
            if (is_static or is_static_pie) {
                try argv.append("--end-group");
            } else {}
            if (is_iamcu) {
                try argv.ensureUnusedCapacity(3);
                argv.appendAssumeCapacity("--as-needed");
                argv.appendAssumeCapacity("-lsoftfp");
                argv.appendAssumeCapacity("--no-as-needed");
            }
        }
        if (!d.nostartfiles and !is_iamcu) {
            // TODO: handle CRT begin/end files
            if (!is_android) {
                try argv.append(try tc.getFilePath("crtn.o"));
            }
        }
    }

    // TODO add -T args
}

fn getMultiarchTriple(target: std.Target) []const u8 {
    const is_android = target.isAndroid();

    return switch (target.cpu.arch) {
        .aarch64 => if (is_android) "aarch64-linux-android" else "aarch64-linux-gnu",
        .aarch64_be => "aarch64_be-linux-gnu",
        .x86 => if (is_android) "i686-linux-android" else "i386-linux-gnu",
        .x86_64 => if (is_android) "x86_64-linux-android" else if (target.abi == .gnux32) "x86_64-linux-gnux32" else "x86_64-linux-gnu",

        // TODO: expand this
        else => "",
    };
}

fn getOSLibDir(target: std.Target) []const u8 {
    switch (target.cpu.arch) {
        .x86,
        .powerpc,
        .powerpcle,
        .sparc,
        .sparcel,
        => return "lib32",
        else => {},
    }
    if (target.cpu.arch == .x86_64 and (target.abi == .gnux32 or target.abi == .muslx32)) {
        return "libx32";
    }
    if (target.cpu.arch == .riscv32) {
        return "lib32";
    }
    if (target.ptrBitWidth() == 32) {
        return "lib";
    }
    return "lib64";
}
