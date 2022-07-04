pub const StringId = enum(u32) {
    pub const Mapper = struct {
        lookup: fn (
            mapper: *const Mapper,
            string_id: StringId,
        ) []const u8,
    };
    pub fn lookup(self: StringId, mapper: *const StringId.Mapper) []const u8 {
        return mapper.lookup(mapper, self);
    }
    empty = 0xFFFF_FFFF,
    _,
};
