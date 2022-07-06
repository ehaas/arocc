pub const StringId = enum(u32) {
    pub const Mapper = struct {
        lookup: fn (
            mapper: @This(),
            string_id: StringId,
        ) []const u8,
    };
    pub fn lookup(self: @This(), mapper: *StringId.Mapper) []const u8 {
        return mapper.lookup(mapper, self);
    }
    empty = 0xFFFF_FFFF,
    _,
};
