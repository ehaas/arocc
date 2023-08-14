const std = @import("std");
const builtin = @import("builtin");
const Compilation = @import("../Compilation.zig");

fn getDefaultTempDir(erase_on_reboot: bool) []const u8 {
    if (erase_on_reboot) {
        return "/tmp";
    }
    return "/var/tmp";
}

fn getEnvTmp(env: Compilation.Environment) ?[]const u8 {
    return env.get("TMPDIR") orelse env.get("TMP") orelse env.get("TEMP") orelse env.get("TEMPDIR");
}

fn getDarwinConfDir(erase_on_reboot: bool) ?[]const u8 {
    if (builtin.target.isDarwin() and builtin.link_libc) {
        const c = @cImport({
            @cInclude("<unistd.h>");
        });
        const name = if (erase_on_reboot) c._CS_DARWIN_USER_TEMP_DIR else c._CS_DARWIN_USER_CACHE_DIR;
        _ = name;
        std.debug.print("hello", .{});
    }
    return null;
}

pub fn tmpDir(env: Compilation.Environment, erase_on_reboot: bool) []const u8 {
    if (erase_on_reboot) {
        if (getEnvTmp(env)) |val| return val;
    }

    if (getDarwinConfDir(erase_on_reboot)) |dir| return dir;

    return getDefaultTempDir(erase_on_reboot);
}
