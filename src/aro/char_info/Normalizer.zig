//! Normalizer contains functions and methods that implement Unicode Normalization algorithms. You can normalize strings
//! into NFC, NFKC, NFD, and NFKD normalization forms (see `nfc`, `nfkc`, `nfd`, and `nfkd`). You can also test for
//! string equality under different parameters related to normalization (see `eql`, `eqlCaseless`, `eqlIdentifiers`).

const std = @import("std");

const ccc_map = @import("derived_combining_class.zig");
const hangul_map = @import("hangul_syllable_type.zig");
const norm_props = @import("derived_normalization_props.zig");
const decompressor = std.compress.deflate.decompressor;

const Self = @This();

nfc_map: std.AutoHashMapUnmanaged([2]u21, u21) = .{},
nfd_map: std.AutoHashMapUnmanaged(u21, [2]u21) = .{},
nfkd_map: std.AutoHashMapUnmanaged(u21, [18]u21) = .{},

pub fn init(allocator: std.mem.Allocator) !Self {
    const comp_file = @embedFile("../../data/unicode/canonical_compositions.txt");
    const decomp_file = @embedFile("../../data/unicode/canonical_decompositions.txt");
    const dekomp_file = @embedFile("../../data/unicode/compatibility_decompositions.txt");

    var buf: [128]u8 = undefined;

    var self: Self = .{};
    errdefer self.deinit(allocator);

    try self.nfc_map.ensureTotalCapacity(allocator, @intCast(std.mem.count(u8, comp_file, "\n")));
    try self.nfd_map.ensureTotalCapacity(allocator, @intCast(std.mem.count(u8, decomp_file, "\n")));
    try self.nfkd_map.ensureTotalCapacity(allocator, @intCast(std.mem.count(u8, dekomp_file, "\n")));

    // Canonical compositions
    var comp_stream = std.io.fixedBufferStream(comp_file);
    const comp_reader = comp_stream.reader();

    while (try comp_reader.readUntilDelimiterOrEof(&buf, '\n')) |line| {
        if (line.len == 0) continue;
        var fields = std.mem.split(u8, line, ";");
        const cp_a = try std.fmt.parseInt(u21, fields.next().?, 16);
        const cp_b = try std.fmt.parseInt(u21, fields.next().?, 16);
        const cp_c = try std.fmt.parseInt(u21, fields.next().?, 16);
        self.nfc_map.putAssumeCapacity(.{ cp_a, cp_b }, cp_c);
    }

    // Canonical decompositions
    var decomp_stream = std.io.fixedBufferStream(decomp_file);
    const decomp_reader = decomp_stream.reader();

    while (try decomp_reader.readUntilDelimiterOrEof(&buf, '\n')) |line| {
        if (line.len == 0) continue;
        var fields = std.mem.split(u8, line, ";");
        const cp_a = try std.fmt.parseInt(u21, fields.next().?, 16);
        const cp_b = try std.fmt.parseInt(u21, fields.next().?, 16);
        const cp_c = try std.fmt.parseInt(u21, fields.next().?, 16);
        self.nfd_map.putAssumeCapacity(cp_a, .{ cp_b, cp_c });
    }

    // Compatibility decompositions
    var dekomp_stream = std.io.fixedBufferStream(dekomp_file);
    const dekomp_reader = dekomp_stream.reader();

    while (try dekomp_reader.readUntilDelimiterOrEof(&buf, '\n')) |line| {
        if (line.len == 0) continue;
        var fields = std.mem.split(u8, line, ";");
        const cp_a = try std.fmt.parseInt(u21, fields.next().?, 16);
        var cps = [_]u21{0} ** 18;
        var i: usize = 0;

        while (fields.next()) |cp| : (i += 1) {
            cps[i] = try std.fmt.parseInt(u21, cp, 16);
        }

        self.nfkd_map.putAssumeCapacity(cp_a, cps);
    }

    return self;
}

pub fn deinit(self: *Self, allocator: std.mem.Allocator) void {
    self.nfc_map.deinit(allocator);
    self.nfd_map.deinit(allocator);
    self.nfkd_map.deinit(allocator);
}

// Hangul processing utilities.
fn isHangulPrecomposed(cp: u21) bool {
    if (hangul_map.syllableType(cp)) |kind| return kind == .LV or kind == .LVT;
    return false;
}

const SBase: u21 = 0xAC00;
const LBase: u21 = 0x1100;
const VBase: u21 = 0x1161;
const TBase: u21 = 0x11A7;
const LCount: u21 = 19;
const VCount: u21 = 21;
const TCount: u21 = 28;
const NCount: u21 = 588; // VCount * TCount
const SCount: u21 = 11172; // LCount * NCount

fn decomposeHangul(cp: u21) [3]u21 {
    const SIndex: u21 = cp - SBase;
    const LIndex: u21 = SIndex / NCount;
    const VIndex: u21 = (SIndex % NCount) / TCount;
    const TIndex: u21 = SIndex % TCount;
    const LPart: u21 = LBase + LIndex;
    const VPart: u21 = VBase + VIndex;
    var TPart: u21 = 0;
    if (TIndex != 0) TPart = TBase + TIndex;

    return [3]u21{ LPart, VPart, TPart };
}

fn composeHangulCanon(lv: u21, t: u21) u21 {
    std.debug.assert(0x11A8 <= t and t <= 0x11C2);
    return lv + (t - TBase);
}

fn composeHangulFull(l: u21, v: u21, t: u21) u21 {
    std.debug.assert(0x1100 <= l and l <= 0x1112);
    std.debug.assert(0x1161 <= v and v <= 0x1175);
    const LIndex = l - LBase;
    const VIndex = v - VBase;
    const LVIndex = LIndex * NCount + VIndex * TCount;

    if (t == 0) return SBase + LVIndex;

    std.debug.assert(0x11A8 <= t and t <= 0x11C2);
    const TIndex = t - TBase;

    return SBase + LVIndex + TIndex;
}

const Form = enum {
    nfc,
    nfd,
    nfkc,
    nfkd,
    same,
};

const Decomp = struct {
    form: Form = .nfd,
    cps: [18]u21 = [_]u21{0} ** 18,
};

/// `mapping` retrieves the decomposition mapping for a code point as per the UCD.
pub fn mapping(self: Self, cp: u21) Decomp {
    var dc = Decomp{ .form = .same };
    dc.cps[0] = cp;

    if (self.nfkd_map.contains(cp)) {
        // do nothing
    } else if (self.nfd_map.get(cp)) |array| {
        dc.form = .nfd;
        @memcpy(dc.cps[0..array.len], &array);
    }

    return dc;
}

/// `decompose` a code point to the specified normalization form, which should be either `.nfd` or `.nfkd`.
pub fn decompose(self: Self, cp: u21) Decomp {
    var dc = Decomp{ .form = .nfd };

    // ASCII or NFD / NFKD quick checks.
    if (cp <= 127 or norm_props.isNfd(cp)) {
        dc.cps[0] = cp;
        return dc;
    }

    // Hangul precomposed syllable full decomposition.
    if (isHangulPrecomposed(cp)) {
        const cps = decomposeHangul(cp);
        std.mem.copy(u21, &dc.cps, &cps);
        return dc;
    }

    // Full decomposition.
    var result_index: usize = 0;
    var work_index: usize = 1;

    // Start work with argument code point.
    var work = [_]u21{cp} ++ [_]u21{0} ** 17;

    while (work_index > 0) {
        // Look at previous code point in work queue.
        work_index -= 1;
        const next = work[work_index];
        const m = self.mapping(next);

        // No more of decompositions for this code point.
        if (m.form == .same) {
            dc.cps[result_index] = m.cps[0];
            result_index += 1;
            continue;
        }

        // Find last index of decomposition.
        const m_last = for (m.cps, 0..) |mcp, i| {
            if (mcp == 0) break i;
        } else m.cps.len;

        // Work backwards through decomposition.
        // `i` starts at 1 because m_last is 1 past the last code point.
        var i: usize = 1;
        while (i <= m_last) : ({
            i += 1;
            work_index += 1;
        }) {
            work[work_index] = m.cps[m_last - i];
        }
    }

    return dc;
}

// Some quick checks.

fn onlyAscii(str: []const u8) bool {
    return for (str) |b| {
        if (b > 127) break false;
    } else true;
}

fn onlyLatin1(str: []const u8) bool {
    var cp_iter = std.unicode.Utf8View.initUnchecked(str).iterator();
    return while (cp_iter.nextCodepoint()) |cp| {
        if (cp > 256) break false;
    } else true;
}

/// Returned from various functions in this namespace. Remember to call `deinit` to free any allocated memory.
pub const Result = struct {
    allocator: ?std.mem.Allocator = null,
    slice: []const u8,

    pub fn deinit(self: *Result) void {
        if (self.allocator) |allocator| allocator.free(self.slice);
    }
};

// Compares code points by Canonical Combining Class order.
fn cccLess(_: void, lhs: u21, rhs: u21) bool {
    return ccc_map.combiningClass(lhs) < ccc_map.combiningClass(rhs);
}

// Applies the Canonical Sorting Algorithm.
fn canonicalSort(cps: []u21) void {
    var i: usize = 0;
    while (i < cps.len) : (i += 1) {
        var start: usize = i;
        while (i < cps.len and ccc_map.combiningClass(cps[i]) != 0) : (i += 1) {}
        std.mem.sort(u21, cps[start..i], {}, cccLess);
    }
}

/// Normalize `str` to NFD.
pub fn nfd(self: Self, allocator: std.mem.Allocator, str: []const u8) !Result {
    return self.nfxd(allocator, str);
}

fn nfxd(self: Self, allocator: std.mem.Allocator, str: []const u8) !Result {
    // Quick checks.
    if (onlyAscii(str)) return Result{ .slice = str };

    var dcp_list = try std.ArrayList(u21).initCapacity(allocator, str.len + str.len / 2);
    defer dcp_list.deinit();

    var cp_iter = std.unicode.Utf8View.initUnchecked(str).iterator();
    while (cp_iter.nextCodepoint()) |cp| {
        const dc = self.decompose(cp);
        const slice = for (dc.cps, 0..) |dcp, i| {
            if (dcp == 0) break dc.cps[0..i];
        } else dc.cps[0..];
        try dcp_list.appendSlice(slice);
    }

    canonicalSort(dcp_list.items);

    var dstr_list = try std.ArrayList(u8).initCapacity(allocator, dcp_list.items.len * 4);
    defer dstr_list.deinit();

    var buf: [4]u8 = undefined;
    for (dcp_list.items) |dcp| {
        const len = try std.unicode.utf8Encode(dcp, &buf);
        dstr_list.appendSliceAssumeCapacity(buf[0..len]);
    }

    return Result{ .allocator = allocator, .slice = try dstr_list.toOwnedSlice() };
}

// Composition utilities.

fn isHangul(cp: u21) bool {
    return cp >= 0x1100 and hangul_map.syllableType(cp) != null;
}

fn isStarter(cp: u21) bool {
    return ccc_map.combiningClass(cp) == 0;
}

fn isCombining(cp: u21) bool {
    return ccc_map.combiningClass(cp) != 0;
}

fn isNonHangulStarter(cp: u21) bool {
    return !isHangul(cp) and isStarter(cp);
}

/// Normalizes `str` to NFC.
pub fn nfc(self: Self, allocator: std.mem.Allocator, str: []const u8) !Result {
    // Quick checks.
    if (onlyLatin1(str)) return Result{ .slice = str };

    // Decompose first.
    var d_result = try self.nfd(allocator, str);
    defer d_result.deinit();

    // Get code points.
    var cp_iter = std.unicode.Utf8View.initUnchecked(d_result.slice).iterator();

    var d_list = try std.ArrayList(u21).initCapacity(allocator, d_result.slice.len);
    defer d_list.deinit();

    while (cp_iter.nextCodepoint()) |cp| d_list.appendAssumeCapacity(cp);

    // Compose
    const tombstone = 0xe000; // Start of BMP Private Use Area

    while (true) {
        var i: usize = 1; // start at second code point.
        var deleted: usize = 0;

        block_check: while (i < d_list.items.len) : (i += 1) {
            const C = d_list.items[i];
            var starter_index: ?usize = null;
            var j: usize = i;

            while (true) {
                j -= 1;

                // Check for starter.
                if (ccc_map.combiningClass(d_list.items[j]) == 0) {
                    if (i - j > 1) { // If there's distance between the starting point and the current position.
                        for (d_list.items[(j + 1)..i]) |B| {
                            // Check for blocking conditions.
                            if (isHangul(C)) {
                                if (isCombining(B) or isNonHangulStarter(B)) continue :block_check;
                            }
                            if (ccc_map.combiningClass(B) >= ccc_map.combiningClass(C)) continue :block_check;
                        }
                    }

                    // Found starter at j.
                    starter_index = j;
                    break;
                }

                if (j == 0) break;
            }

            if (starter_index) |sidx| {
                const L = d_list.items[sidx];
                var processed_hangul = false;

                if (isHangul(L) and isHangul(C)) {
                    const l_stype = hangul_map.syllableType(L).?;
                    const c_stype = hangul_map.syllableType(C).?;

                    if (l_stype == .LV and c_stype == .T) {
                        // LV, T
                        d_list.items[sidx] = composeHangulCanon(L, C);
                        d_list.items[i] = tombstone; // Mark for deletion.
                        processed_hangul = true;
                    }

                    if (l_stype == .L and c_stype == .V) {
                        // Handle L, V. L, V, T is handled via main loop.
                        d_list.items[sidx] = composeHangulFull(L, C, 0);
                        d_list.items[i] = tombstone; // Mark for deletion.
                        processed_hangul = true;
                    }

                    if (processed_hangul) deleted += 1;
                }

                if (!processed_hangul) {
                    // L -> C not Hangul.
                    if (self.nfc_map.get(.{ L, C })) |P| {
                        if (!norm_props.isFcx(P)) {
                            d_list.items[sidx] = P;
                            d_list.items[i] = tombstone; // Mark for deletion.
                            deleted += 1;
                        }
                    }
                }
            }
        }

        // Check if finished.
        if (deleted == 0) {
            var cstr_list = try std.ArrayList(u8).initCapacity(allocator, d_list.items.len * 4);
            defer cstr_list.deinit();
            var buf: [4]u8 = undefined;

            for (d_list.items) |cp| {
                if (cp == tombstone) continue; // "Delete"
                const len = try std.unicode.utf8Encode(cp, &buf);
                cstr_list.appendSliceAssumeCapacity(buf[0..len]);
            }

            return Result{ .allocator = allocator, .slice = try cstr_list.toOwnedSlice() };
        }

        // Otherwise update code points list.
        var tmp_d_list = try std.ArrayList(u21).initCapacity(allocator, d_list.items.len - deleted);
        defer tmp_d_list.deinit();

        for (d_list.items) |cp| {
            if (cp != tombstone) tmp_d_list.appendAssumeCapacity(cp);
        }

        d_list.clearRetainingCapacity();
        d_list.appendSliceAssumeCapacity(tmp_d_list.items);
    }
}
