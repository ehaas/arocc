const std = @import("std");
const builtin = @import("builtin");
const assert = std.debug.assert;
const autoHash = std.hash.autoHash;
const math = std.math;
const mem = std.mem;
const meta = std.meta;
const Allocator = mem.Allocator;
const Wyhash = std.hash.Wyhash;

pub fn getAutoHashFn(comptime K: type, comptime Context: type) (fn (Context, K) u64) {
    comptime {
        assert(@hasDecl(std, "StringHashMap")); // detect when the following message needs updated
        if (K == []const u8) {
            @compileError("std.auto_hash.autoHash does not allow slices here (" ++
                @typeName(K) ++
                ") because the intent is unclear. " ++
                "Consider using std.StringHashMap for hashing the contents of []const u8. " ++
                "Alternatively, consider using std.auto_hash.hash or providing your own hash function instead.");
        }
    }

    return struct {
        fn hash(ctx: Context, key: K) u64 {
            _ = ctx;
            if (comptime meta.hasUniqueRepresentation(K)) {
                return Wyhash.hash(0, std.mem.asBytes(&key));
            } else {
                var hasher = Wyhash.init(0);
                autoHash(&hasher, key);
                return hasher.final();
            }
        }
    }.hash;
}

pub fn getAutoEqlFn(comptime K: type, comptime Context: type) (fn (Context, K, K) bool) {
    return struct {
        fn eql(ctx: Context, a: K, b: K) bool {
            _ = ctx;
            return meta.eql(a, b);
        }
    }.eql;
}

pub fn AutoHashMap(comptime K: type, comptime V: type) type {
    return HashMap(K, V, AutoContext(K), default_max_load_percentage);
}

pub fn AutoHashMapUnmanaged(comptime K: type, comptime V: type) type {
    return HashMapUnmanaged(K, V, AutoContext(K), default_max_load_percentage);
}

pub fn AutoContext(comptime K: type) type {
    return struct {
        pub const hash = getAutoHashFn(K, @This());
        pub const eql = getAutoEqlFn(K, @This());
    };
}

/// Builtin hashmap for strings as keys.
/// Key memory is managed by the caller.  Keys and values
/// will not automatically be freed.
pub fn StringHashMap(comptime V: type) type {
    return HashMap([]const u8, V, StringContext, default_max_load_percentage);
}

/// Key memory is managed by the caller.  Keys and values
/// will not automatically be freed.
pub fn StringHashMapUnmanaged(comptime V: type) type {
    return HashMapUnmanaged([]const u8, V, StringContext, default_max_load_percentage);
}

pub const StringContext = struct {
    pub fn hash(self: @This(), s: []const u8) u64 {
        _ = self;
        return hashString(s);
    }
    pub fn eql(self: @This(), a: []const u8, b: []const u8) bool {
        _ = self;
        return eqlString(a, b);
    }
};

pub fn eqlString(a: []const u8, b: []const u8) bool {
    return mem.eql(u8, a, b);
}

pub fn hashString(s: []const u8) u64 {
    return std.hash.Wyhash.hash(0, s);
}

pub const StringIndexContext = struct {
    bytes: *const std.ArrayListUnmanaged(u8),

    pub fn eql(self: @This(), a: u32, b: u32) bool {
        _ = self;
        return a == b;
    }

    pub fn hash(self: @This(), x: u32) u64 {
        const x_slice = mem.sliceTo(@as([*:0]const u8, @ptrCast(self.bytes.items.ptr)) + x, 0);
        return hashString(x_slice);
    }
};

pub const StringIndexAdapter = struct {
    bytes: *const std.ArrayListUnmanaged(u8),

    pub fn eql(self: @This(), a_slice: []const u8, b: u32) bool {
        const b_slice = mem.sliceTo(@as([*:0]const u8, @ptrCast(self.bytes.items.ptr)) + b, 0);
        return mem.eql(u8, a_slice, b_slice);
    }

    pub fn hash(self: @This(), adapted_key: []const u8) u64 {
        _ = self;
        return hashString(adapted_key);
    }
};

pub const default_max_load_percentage = 80;

/// This function issues a compile error with a helpful message if there
/// is a problem with the provided context type.  A context must have the following
/// member functions:
///   - hash(self, PseudoKey) Hash
///   - eql(self, PseudoKey, Key) bool
///
/// If you are passing a context to a *Adapted function, PseudoKey is the type
/// of the key parameter.  Otherwise, when creating a HashMap or HashMapUnmanaged
/// type, PseudoKey = Key = K.
pub fn verifyContext(
    comptime RawContext: type,
    comptime PseudoKey: type,
    comptime Key: type,
    comptime Hash: type,
    comptime is_array: bool,
) void {
    comptime {
        var allow_const_ptr = false;
        var allow_mutable_ptr = false;
        // Context is the actual namespace type.  RawContext may be a pointer to Context.
        var Context = RawContext;
        // Make sure the context is a namespace type which may have member functions
        switch (@typeInfo(Context)) {
            .Struct, .Union, .Enum => {},
            // Special-case .Opaque for a better error message
            .Opaque => @compileError("Hash context must be a type with hash and eql member functions.  Cannot use " ++ @typeName(Context) ++ " because it is opaque.  Use a pointer instead."),
            .Pointer => |ptr| {
                if (ptr.size != .One) {
                    @compileError("Hash context must be a type with hash and eql member functions.  Cannot use " ++ @typeName(Context) ++ " because it is not a single pointer.");
                }
                Context = ptr.child;
                allow_const_ptr = true;
                allow_mutable_ptr = !ptr.is_const;
                switch (@typeInfo(Context)) {
                    .Struct, .Union, .Enum, .Opaque => {},
                    else => @compileError("Hash context must be a type with hash and eql member functions.  Cannot use " ++ @typeName(Context)),
                }
            },
            else => @compileError("Hash context must be a type with hash and eql member functions.  Cannot use " ++ @typeName(Context)),
        }

        // Keep track of multiple errors so we can report them all.
        var errors: []const u8 = "";

        // Put common errors here, they will only be evaluated
        // if the error is actually triggered.
        const lazy = struct {
            const prefix = "\n  ";
            const deep_prefix = prefix ++ "  ";
            const hash_signature = "fn (self, " ++ @typeName(PseudoKey) ++ ") " ++ @typeName(Hash);
            const index_param = if (is_array) ", b_index: usize" else "";
            const eql_signature = "fn (self, " ++ @typeName(PseudoKey) ++ ", " ++
                @typeName(Key) ++ index_param ++ ") bool";
            const err_invalid_hash_signature = prefix ++ @typeName(Context) ++ ".hash must be " ++ hash_signature ++
                deep_prefix ++ "but is actually " ++ @typeName(@TypeOf(Context.hash));
            const err_invalid_eql_signature = prefix ++ @typeName(Context) ++ ".eql must be " ++ eql_signature ++
                deep_prefix ++ "but is actually " ++ @typeName(@TypeOf(Context.eql));
        };

        // Verify Context.hash(self, PseudoKey) => Hash
        if (@hasDecl(Context, "hash")) {
            const hash = Context.hash;
            const info = @typeInfo(@TypeOf(hash));
            if (info == .Fn) {
                const func = info.Fn;
                if (func.params.len != 2) {
                    errors = errors ++ lazy.err_invalid_hash_signature;
                } else {
                    var emitted_signature = false;
                    if (func.params[0].type) |Self| {
                        if (Self == Context) {
                            // pass, this is always fine.
                        } else if (Self == *const Context) {
                            if (!allow_const_ptr) {
                                if (!emitted_signature) {
                                    errors = errors ++ lazy.err_invalid_hash_signature;
                                    emitted_signature = true;
                                }
                                errors = errors ++ lazy.deep_prefix ++ "First parameter must be " ++ @typeName(Context) ++ ", but is " ++ @typeName(Self);
                                errors = errors ++ lazy.deep_prefix ++ "Note: Cannot be a pointer because it is passed by value.";
                            }
                        } else if (Self == *Context) {
                            if (!allow_mutable_ptr) {
                                if (!emitted_signature) {
                                    errors = errors ++ lazy.err_invalid_hash_signature;
                                    emitted_signature = true;
                                }
                                if (!allow_const_ptr) {
                                    errors = errors ++ lazy.deep_prefix ++ "First parameter must be " ++ @typeName(Context) ++ ", but is " ++ @typeName(Self);
                                    errors = errors ++ lazy.deep_prefix ++ "Note: Cannot be a pointer because it is passed by value.";
                                } else {
                                    errors = errors ++ lazy.deep_prefix ++ "First parameter must be " ++ @typeName(Context) ++ " or " ++ @typeName(*const Context) ++ ", but is " ++ @typeName(Self);
                                    errors = errors ++ lazy.deep_prefix ++ "Note: Cannot be non-const because it is passed by const pointer.";
                                }
                            }
                        } else {
                            if (!emitted_signature) {
                                errors = errors ++ lazy.err_invalid_hash_signature;
                                emitted_signature = true;
                            }
                            errors = errors ++ lazy.deep_prefix ++ "First parameter must be " ++ @typeName(Context);
                            if (allow_const_ptr) {
                                errors = errors ++ " or " ++ @typeName(*const Context);
                                if (allow_mutable_ptr) {
                                    errors = errors ++ " or " ++ @typeName(*Context);
                                }
                            }
                            errors = errors ++ ", but is " ++ @typeName(Self);
                        }
                    }
                    if (func.params[1].type != null and func.params[1].type.? != PseudoKey) {
                        if (!emitted_signature) {
                            errors = errors ++ lazy.err_invalid_hash_signature;
                            emitted_signature = true;
                        }
                        errors = errors ++ lazy.deep_prefix ++ "Second parameter must be " ++ @typeName(PseudoKey) ++ ", but is " ++ @typeName(func.params[1].type.?);
                    }
                    if (func.return_type != null and func.return_type.? != Hash) {
                        if (!emitted_signature) {
                            errors = errors ++ lazy.err_invalid_hash_signature;
                            emitted_signature = true;
                        }
                        errors = errors ++ lazy.deep_prefix ++ "Return type must be " ++ @typeName(Hash) ++ ", but was " ++ @typeName(func.return_type.?);
                    }
                    // If any of these are generic (null), we cannot verify them.
                    // The call sites check the return type, but cannot check the
                    // parameters.  This may cause compile errors with generic hash/eql functions.
                }
            } else {
                errors = errors ++ lazy.err_invalid_hash_signature;
            }
        } else {
            errors = errors ++ lazy.prefix ++ @typeName(Context) ++ " must declare a hash function with signature " ++ lazy.hash_signature;
        }

        // Verify Context.eql(self, PseudoKey, Key) => bool
        if (@hasDecl(Context, "eql")) {
            const eql = Context.eql;
            const info = @typeInfo(@TypeOf(eql));
            if (info == .Fn) {
                const func = info.Fn;
                const args_len = if (is_array) 4 else 3;
                if (func.params.len != args_len) {
                    errors = errors ++ lazy.err_invalid_eql_signature;
                } else {
                    var emitted_signature = false;
                    if (func.params[0].type) |Self| {
                        if (Self == Context) {
                            // pass, this is always fine.
                        } else if (Self == *const Context) {
                            if (!allow_const_ptr) {
                                if (!emitted_signature) {
                                    errors = errors ++ lazy.err_invalid_eql_signature;
                                    emitted_signature = true;
                                }
                                errors = errors ++ lazy.deep_prefix ++ "First parameter must be " ++ @typeName(Context) ++ ", but is " ++ @typeName(Self);
                                errors = errors ++ lazy.deep_prefix ++ "Note: Cannot be a pointer because it is passed by value.";
                            }
                        } else if (Self == *Context) {
                            if (!allow_mutable_ptr) {
                                if (!emitted_signature) {
                                    errors = errors ++ lazy.err_invalid_eql_signature;
                                    emitted_signature = true;
                                }
                                if (!allow_const_ptr) {
                                    errors = errors ++ lazy.deep_prefix ++ "First parameter must be " ++ @typeName(Context) ++ ", but is " ++ @typeName(Self);
                                    errors = errors ++ lazy.deep_prefix ++ "Note: Cannot be a pointer because it is passed by value.";
                                } else {
                                    errors = errors ++ lazy.deep_prefix ++ "First parameter must be " ++ @typeName(Context) ++ " or " ++ @typeName(*const Context) ++ ", but is " ++ @typeName(Self);
                                    errors = errors ++ lazy.deep_prefix ++ "Note: Cannot be non-const because it is passed by const pointer.";
                                }
                            }
                        } else {
                            if (!emitted_signature) {
                                errors = errors ++ lazy.err_invalid_eql_signature;
                                emitted_signature = true;
                            }
                            errors = errors ++ lazy.deep_prefix ++ "First parameter must be " ++ @typeName(Context);
                            if (allow_const_ptr) {
                                errors = errors ++ " or " ++ @typeName(*const Context);
                                if (allow_mutable_ptr) {
                                    errors = errors ++ " or " ++ @typeName(*Context);
                                }
                            }
                            errors = errors ++ ", but is " ++ @typeName(Self);
                        }
                    }
                    if (func.params[1].type.? != PseudoKey) {
                        if (!emitted_signature) {
                            errors = errors ++ lazy.err_invalid_eql_signature;
                            emitted_signature = true;
                        }
                        errors = errors ++ lazy.deep_prefix ++ "Second parameter must be " ++ @typeName(PseudoKey) ++ ", but is " ++ @typeName(func.params[1].type.?);
                    }
                    if (func.params[2].type.? != Key) {
                        if (!emitted_signature) {
                            errors = errors ++ lazy.err_invalid_eql_signature;
                            emitted_signature = true;
                        }
                        errors = errors ++ lazy.deep_prefix ++ "Third parameter must be " ++ @typeName(Key) ++ ", but is " ++ @typeName(func.params[2].type.?);
                    }
                    if (func.return_type.? != bool) {
                        if (!emitted_signature) {
                            errors = errors ++ lazy.err_invalid_eql_signature;
                            emitted_signature = true;
                        }
                        errors = errors ++ lazy.deep_prefix ++ "Return type must be bool, but was " ++ @typeName(func.return_type.?);
                    }
                    // If any of these are generic (null), we cannot verify them.
                    // The call sites check the return type, but cannot check the
                    // parameters.  This may cause compile errors with generic hash/eql functions.
                }
            } else {
                errors = errors ++ lazy.err_invalid_eql_signature;
            }
        } else {
            errors = errors ++ lazy.prefix ++ @typeName(Context) ++ " must declare a eql function with signature " ++ lazy.eql_signature;
        }

        if (errors.len != 0) {
            // errors begins with a newline (from lazy.prefix)
            @compileError("Problems found with hash context type " ++ @typeName(Context) ++ ":" ++ errors);
        }
    }
}

/// General purpose hash table.
/// No order is guaranteed and any modification invalidates live iterators.
/// It provides fast operations (lookup, insertion, deletion) with quite high
/// load factors (up to 80% by default) for low memory usage.
/// For a hash map that can be initialized directly that does not store an Allocator
/// field, see `HashMapUnmanaged`.
/// If iterating over the table entries is a strong usecase and needs to be fast,
/// prefer the alternative `std.ArrayHashMap`.
/// Context must be a struct type with two member functions:
///   hash(self, K) u64
///   eql(self, K, K) bool
/// Adapted variants of many functions are provided.  These variants
/// take a pseudo key instead of a key.  Their context must have the functions:
///   hash(self, PseudoKey) u64
///   eql(self, PseudoKey, K) bool
pub fn HashMap(
    comptime K: type,
    comptime V: type,
    comptime Context: type,
    comptime max_load_percentage: u64,
) type {
    return struct {
        unmanaged: Unmanaged,
        allocator: Allocator,
        ctx: Context,

        comptime {
            verifyContext(Context, K, K, u64, false);
        }

        /// The type of the unmanaged hash map underlying this wrapper
        pub const Unmanaged = HashMapUnmanaged(K, V, Context, max_load_percentage);
        /// An entry, containing pointers to a key and value stored in the map
        pub const Entry = Unmanaged.Entry;
        /// A copy of a key and value which are no longer in the map
        pub const KV = Unmanaged.KV;
        /// The integer type that is the result of hashing
        pub const Hash = Unmanaged.Hash;
        /// The iterator type returned by iterator()
        pub const Iterator = Unmanaged.Iterator;

        pub const KeyIterator = Unmanaged.KeyIterator;
        pub const ValueIterator = Unmanaged.ValueIterator;

        /// The integer type used to store the size of the map
        pub const Size = Unmanaged.Size;
        /// The type returned from getOrPut and variants
        pub const GetOrPutResult = Unmanaged.GetOrPutResult;

        const Self = @This();

        /// Create a managed hash map with an empty context.
        /// If the context is not zero-sized, you must use
        /// initContext(allocator, ctx) instead.
        pub fn init(allocator: Allocator) Self {
            if (@sizeOf(Context) != 0) {
                @compileError("Context must be specified! Call initContext(allocator, ctx) instead.");
            }
            return .{
                .unmanaged = .{},
                .allocator = allocator,
                .ctx = undefined, // ctx is zero-sized so this is safe.
            };
        }

        /// Create a managed hash map with a context
        pub fn initContext(allocator: Allocator, ctx: Context) Self {
            return .{
                .unmanaged = .{},
                .allocator = allocator,
                .ctx = ctx,
            };
        }

        /// Release the backing array and invalidate this map.
        /// This does *not* deinit keys, values, or the context!
        /// If your keys or values need to be released, ensure
        /// that that is done before calling this function.
        pub fn deinit(self: *Self) void {
            self.unmanaged.deinit(self.allocator);
            self.* = undefined;
        }

        /// Empty the map, but keep the backing allocation for future use.
        /// This does *not* free keys or values! Be sure to
        /// release them if they need deinitialization before
        /// calling this function.
        pub fn clearRetainingCapacity(self: *Self) void {
            return self.unmanaged.clearRetainingCapacity();
        }

        /// Empty the map and release the backing allocation.
        /// This does *not* free keys or values! Be sure to
        /// release them if they need deinitialization before
        /// calling this function.
        pub fn clearAndFree(self: *Self) void {
            return self.unmanaged.clearAndFree(self.allocator);
        }

        /// Return the number of items in the map.
        pub fn count(self: Self) Size {
            return self.unmanaged.count();
        }

        /// Create an iterator over the entries in the map.
        /// The iterator is invalidated if the map is modified.
        pub fn iterator(self: *const Self) Iterator {
            return self.unmanaged.iterator();
        }

        /// Create an iterator over the keys in the map.
        /// The iterator is invalidated if the map is modified.
        pub fn keyIterator(self: *const Self) KeyIterator {
            return self.unmanaged.keyIterator();
        }

        /// Create an iterator over the values in the map.
        /// The iterator is invalidated if the map is modified.
        pub fn valueIterator(self: *const Self) ValueIterator {
            return self.unmanaged.valueIterator();
        }

        /// If key exists this function cannot fail.
        /// If there is an existing item with `key`, then the result's
        /// `Entry` pointers point to it, and found_existing is true.
        /// Otherwise, puts a new item with undefined value, and
        /// the `Entry` pointers point to it. Caller should then initialize
        /// the value (but not the key).
        pub fn getOrPut(self: *Self, key: K) Allocator.Error!GetOrPutResult {
            return self.unmanaged.getOrPutContext(self.allocator, key, self.ctx);
        }

        /// If key exists this function cannot fail.
        /// If there is an existing item with `key`, then the result's
        /// `Entry` pointers point to it, and found_existing is true.
        /// Otherwise, puts a new item with undefined key and value, and
        /// the `Entry` pointers point to it. Caller must then initialize
        /// the key and value.
        pub fn getOrPutAdapted(self: *Self, key: anytype, ctx: anytype) Allocator.Error!GetOrPutResult {
            return self.unmanaged.getOrPutContextAdapted(self.allocator, key, ctx, self.ctx);
        }

        /// If there is an existing item with `key`, then the result's
        /// `Entry` pointers point to it, and found_existing is true.
        /// Otherwise, puts a new item with undefined value, and
        /// the `Entry` pointers point to it. Caller should then initialize
        /// the value (but not the key).
        /// If a new entry needs to be stored, this function asserts there
        /// is enough capacity to store it.
        pub fn getOrPutAssumeCapacity(self: *Self, key: K) GetOrPutResult {
            return self.unmanaged.getOrPutAssumeCapacityContext(key, self.ctx);
        }

        /// If there is an existing item with `key`, then the result's
        /// `Entry` pointers point to it, and found_existing is true.
        /// Otherwise, puts a new item with undefined value, and
        /// the `Entry` pointers point to it. Caller must then initialize
        /// the key and value.
        /// If a new entry needs to be stored, this function asserts there
        /// is enough capacity to store it.
        pub fn getOrPutAssumeCapacityAdapted(self: *Self, key: anytype, ctx: anytype) GetOrPutResult {
            return self.unmanaged.getOrPutAssumeCapacityAdapted(key, ctx);
        }

        pub fn getOrPutValue(self: *Self, key: K, value: V) Allocator.Error!Entry {
            return self.unmanaged.getOrPutValueContext(self.allocator, key, value, self.ctx);
        }

        /// Increases capacity, guaranteeing that insertions up until the
        /// `expected_count` will not cause an allocation, and therefore cannot fail.
        pub fn ensureTotalCapacity(self: *Self, expected_count: Size) Allocator.Error!void {
            return self.unmanaged.ensureTotalCapacityContext(self.allocator, expected_count, self.ctx);
        }

        /// Increases capacity, guaranteeing that insertions up until
        /// `additional_count` **more** items will not cause an allocation, and
        /// therefore cannot fail.
        pub fn ensureUnusedCapacity(self: *Self, additional_count: Size) Allocator.Error!void {
            return self.unmanaged.ensureUnusedCapacityContext(self.allocator, additional_count, self.ctx);
        }

        /// Returns the number of total elements which may be present before it is
        /// no longer guaranteed that no allocations will be performed.
        pub fn capacity(self: *Self) Size {
            return self.unmanaged.capacity();
        }

        /// Clobbers any existing data. To detect if a put would clobber
        /// existing data, see `getOrPut`.
        pub fn put(self: *Self, key: K, value: V) Allocator.Error!void {
            return self.unmanaged.putContext(self.allocator, key, value, self.ctx);
        }

        /// Inserts a key-value pair into the hash map, asserting that no previous
        /// entry with the same key is already present
        pub fn putNoClobber(self: *Self, key: K, value: V) Allocator.Error!void {
            return self.unmanaged.putNoClobberContext(self.allocator, key, value, self.ctx);
        }

        /// Asserts there is enough capacity to store the new key-value pair.
        /// Clobbers any existing data. To detect if a put would clobber
        /// existing data, see `getOrPutAssumeCapacity`.
        pub fn putAssumeCapacity(self: *Self, key: K, value: V) void {
            return self.unmanaged.putAssumeCapacityContext(key, value, self.ctx);
        }

        /// Asserts there is enough capacity to store the new key-value pair.
        /// Asserts that it does not clobber any existing data.
        /// To detect if a put would clobber existing data, see `getOrPutAssumeCapacity`.
        pub fn putAssumeCapacityNoClobber(self: *Self, key: K, value: V) void {
            return self.unmanaged.putAssumeCapacityNoClobberContext(key, value, self.ctx);
        }

        /// Inserts a new `Entry` into the hash map, returning the previous one, if any.
        pub fn fetchPut(self: *Self, key: K, value: V) Allocator.Error!?KV {
            return self.unmanaged.fetchPutContext(self.allocator, key, value, self.ctx);
        }

        /// Inserts a new `Entry` into the hash map, returning the previous one, if any.
        /// If insertion happens, asserts there is enough capacity without allocating.
        pub fn fetchPutAssumeCapacity(self: *Self, key: K, value: V) ?KV {
            return self.unmanaged.fetchPutAssumeCapacityContext(key, value, self.ctx);
        }

        /// Removes a value from the map and returns the removed kv pair.
        pub fn fetchRemove(self: *Self, key: K) ?KV {
            return self.unmanaged.fetchRemoveContext(key, self.ctx);
        }

        pub fn fetchRemoveAdapted(self: *Self, key: anytype, ctx: anytype) ?KV {
            return self.unmanaged.fetchRemoveAdapted(key, ctx);
        }

        /// Finds the value associated with a key in the map
        pub fn get(self: Self, key: K) ?V {
            return self.unmanaged.getContext(key, self.ctx);
        }
        pub fn getAdapted(self: Self, key: anytype, ctx: anytype) ?V {
            return self.unmanaged.getAdapted(key, ctx);
        }

        pub fn getPtr(self: Self, key: K) ?*V {
            return self.unmanaged.getPtrContext(key, self.ctx);
        }
        pub fn getPtrAdapted(self: Self, key: anytype, ctx: anytype) ?*V {
            return self.unmanaged.getPtrAdapted(key, ctx);
        }

        /// Finds the actual key associated with an adapted key in the map
        pub fn getKey(self: Self, key: K) ?K {
            return self.unmanaged.getKeyContext(key, self.ctx);
        }
        pub fn getKeyAdapted(self: Self, key: anytype, ctx: anytype) ?K {
            return self.unmanaged.getKeyAdapted(key, ctx);
        }

        pub fn getKeyPtr(self: Self, key: K) ?*K {
            return self.unmanaged.getKeyPtrContext(key, self.ctx);
        }
        pub fn getKeyPtrAdapted(self: Self, key: anytype, ctx: anytype) ?*K {
            return self.unmanaged.getKeyPtrAdapted(key, ctx);
        }

        /// Finds the key and value associated with a key in the map
        pub fn getEntry(self: Self, key: K) ?Entry {
            return self.unmanaged.getEntryContext(key, self.ctx);
        }

        pub fn getEntryAdapted(self: Self, key: anytype, ctx: anytype) ?Entry {
            return self.unmanaged.getEntryAdapted(key, ctx);
        }

        /// Check if the map contains a key
        pub fn contains(self: Self, key: K) bool {
            return self.unmanaged.containsContext(key, self.ctx);
        }

        pub fn containsAdapted(self: Self, key: anytype, ctx: anytype) bool {
            return self.unmanaged.containsAdapted(key, ctx);
        }

        /// If there is an `Entry` with a matching key, it is deleted from
        /// the hash map, and this function returns true.  Otherwise this
        /// function returns false.
        pub fn remove(self: *Self, key: K) bool {
            return self.unmanaged.removeContext(key, self.ctx);
        }

        pub fn removeAdapted(self: *Self, key: anytype, ctx: anytype) bool {
            return self.unmanaged.removeAdapted(key, ctx);
        }

        /// Delete the entry with key pointed to by key_ptr from the hash map.
        /// key_ptr is assumed to be a valid pointer to a key that is present
        /// in the hash map.
        pub fn removeByPtr(self: *Self, key_ptr: *K) void {
            self.unmanaged.removeByPtr(key_ptr);
        }

        /// Creates a copy of this map, using the same allocator
        pub fn clone(self: Self) Allocator.Error!Self {
            var other = try self.unmanaged.cloneContext(self.allocator, self.ctx);
            return other.promoteContext(self.allocator, self.ctx);
        }

        /// Creates a copy of this map, using a specified allocator
        pub fn cloneWithAllocator(self: Self, new_allocator: Allocator) Allocator.Error!Self {
            var other = try self.unmanaged.cloneContext(new_allocator, self.ctx);
            return other.promoteContext(new_allocator, self.ctx);
        }

        /// Creates a copy of this map, using a specified context
        pub fn cloneWithContext(self: Self, new_ctx: anytype) Allocator.Error!HashMap(K, V, @TypeOf(new_ctx), max_load_percentage) {
            var other = try self.unmanaged.cloneContext(self.allocator, new_ctx);
            return other.promoteContext(self.allocator, new_ctx);
        }

        /// Creates a copy of this map, using a specified allocator and context.
        pub fn cloneWithAllocatorAndContext(
            self: Self,
            new_allocator: Allocator,
            new_ctx: anytype,
        ) Allocator.Error!HashMap(K, V, @TypeOf(new_ctx), max_load_percentage) {
            var other = try self.unmanaged.cloneContext(new_allocator, new_ctx);
            return other.promoteContext(new_allocator, new_ctx);
        }

        /// Set the map to an empty state, making deinitialization a no-op, and
        /// returning a copy of the original.
        pub fn move(self: *Self) Self {
            const result = self.*;
            self.unmanaged = .{};
            return result;
        }
    };
}

/// A HashMap based on open addressing and linear probing.
/// A lookup or modification typically incurs only 2 cache misses.
/// No order is guaranteed and any modification invalidates live iterators.
/// It achieves good performance with quite high load factors (by default,
/// grow is triggered at 80% full) and only one byte of overhead per element.
/// The struct itself is only 16 bytes for a small footprint. This comes at
/// the price of handling size with u32, which should be reasonable enough
/// for almost all uses.
/// Deletions are achieved with tombstones.
pub fn HashMapUnmanaged(
    comptime K: type,
    comptime V: type,
    comptime Context: type,
    comptime max_load_percentage: u64,
) type {
    if (max_load_percentage <= 0 or max_load_percentage >= 100)
        @compileError("max_load_percentage must be between 0 and 100.");
    return struct {
        const Self = @This();

        comptime {
            verifyContext(Context, K, K, u64, false);
        }

        // This is actually a midway pointer to the single buffer containing
        // a `Header` field, the `Metadata`s and `Entry`s.
        // At `-@sizeOf(Header)` is the Header field.
        // At `sizeOf(Metadata) * capacity + offset`, which is pointed to by
        // self.header().entries, is the array of entries.
        // This means that the hashmap only holds one live allocation, to
        // reduce memory fragmentation and struct size.
        /// Pointer to the metadata.
        metadata: ?[*]Metadata = null,

        /// Current number of elements in the hashmap.
        size: Size = 0,

        // Having a countdown to grow reduces the number of instructions to
        // execute when determining if the hashmap has enough capacity already.
        /// Number of available slots before a grow is needed to satisfy the
        /// `max_load_percentage`.
        available: Size = 0,

        // This is purely empirical and not a /very smart magic constant™/.
        /// Capacity of the first grow when bootstrapping the hashmap.
        const minimal_capacity = 8;

        // This hashmap is specially designed for sizes that fit in a u32.
        pub const Size = u32;

        // u64 hashes guarantee us that the fingerprint bits will never be used
        // to compute the index of a slot, maximizing the use of entropy.
        pub const Hash = u64;

        pub const Entry = struct {
            key_ptr: *K,
            value_ptr: *V,
        };

        pub const KV = struct {
            key: K,
            value: V,
        };

        const Header = struct {
            values: [*]V,
            keys: [*]K,
            capacity: Size,
        };

        /// Metadata for a slot. It can be in three states: empty, used or
        /// tombstone. Tombstones indicate that an entry was previously used,
        /// they are a simple way to handle removal.
        /// To this state, we add 7 bits from the slot's key hash. These are
        /// used as a fast way to disambiguate between entries without
        /// having to use the equality function. If two fingerprints are
        /// different, we know that we don't have to compare the keys at all.
        /// The 7 bits are the highest ones from a 64 bit hash. This way, not
        /// only we use the `log2(capacity)` lowest bits from the hash to determine
        /// a slot index, but we use 7 more bits to quickly resolve collisions
        /// when multiple elements with different hashes end up wanting to be in the same slot.
        /// Not using the equality function means we don't have to read into
        /// the entries array, likely avoiding a cache miss and a potentially
        /// costly function call.
        const Metadata = packed struct(u8) {
            const FingerPrint = u7;
            fingerprint: FingerPrint,
            used: u1,

            pub const empty = Metadata{ .fingerprint = 0, .used = 0 };
            pub const tombstone = Metadata{ .fingerprint = 1, .used = 0 };

            pub fn takeFingerprint(hash: Hash) Metadata {
                const hash_bits = @typeInfo(Hash).Int.bits;
                const fp_bits = @typeInfo(FingerPrint).Int.bits;
                return .{ .fingerprint = @truncate(hash >> (hash_bits - fp_bits)), .used = 1 };
            }
        };

        comptime {
            assert(@sizeOf(Metadata) == 1);
            assert(@alignOf(Metadata) == 1);
        }

        /// Platform-efficient method for matching on a chunk/lane of Metadata, returning a bit Mask
        /// whose indexes can be iterated on using `@ctz(mask) >> Scan.shift`.
        const Scan = struct {
            pub const Matcher = union(enum) {
                eq: Metadata,
                used,
                empty,
                empty_or_tombstone,
            };

            pub const lanes = @sizeOf(@This().Input);
            pub const Mask = @TypeOf(@This().match(.used, undefined));

            pub inline fn read(metadata: [*]const Metadata) @This().Input {
                var input: @This().Input = @bitCast(metadata[0..lanes].*);
                if (builtin.cpu.arch.endian() == .big) input = @byteSwap(input);
                return input;
            }

            pub usingnamespace blk: {
                if (builtin.cpu.arch.isX86() and builtin.zig_backend != .stage2_x86_64) {
                    if (std.Target.x86.featureSetHas(builtin.cpu.features, .avx2)) break :blk MatchMovemask(32);
                    if (std.Target.x86.featureSetHas(builtin.cpu.features, .sse2)) break :blk MatchMovemask(16);
                }
                if (builtin.cpu.arch.isWASM() and builtin.zig_backend != .stage2_wasm) {
                    if (std.Target.wasm.featureSetHas(builtin.cpu.features, .simd128)) break :blk MatchMovemask(16);
                }
                if (builtin.cpu.arch.isAARCH64() and builtin.zig_backend != .stage2_aarch64) {
                    if (std.Target.aarch64.featureSetHas(builtin.cpu.features, .neon)) break :blk MatchNeon;
                }
                break :blk MatchScalar;
            };

            /// For platforms which support efficiently reducing a vector of bools into an int.
            fn MatchMovemask(comptime vector_size: comptime_int) type {
                return MatchVector(struct {
                    pub const shift = 0;
                    pub const vec_size = vector_size;
                    pub inline fn reduce(cmp: @Vector(vec_size, bool)) std.meta.Int(.unsigned, vec_size) {
                        const cmp_mask: @Vector(vec_size, u1) = @bitCast(cmp);
                        return @bitCast(cmp_mask);
                    }
                });
            }

            /// For platforms which support efficient bool-to-u8-mask and widening/truncating vectors.
            /// https://community.arm.com/arm-community-blogs/b/infrastructure-solutions-blog/posts/porting-x86-vector-bitmask-optimizations-to-arm-neon
            const MatchNeon = MatchVector(struct {
                pub const shift = 2;
                pub const vec_size = 16;
                pub inline fn reduce(cmp: @Vector(16, bool)) u64 {
                    const zero: @Vector(16, u8) = @splat(0);
                    const cmp_mask = @select(u8, cmp, ~zero, zero);
                    const wide_mask: @Vector(8, u16) = @bitCast(cmp_mask);
                    const shift_trunc: @Vector(8, u8) = @bitCast(wide_mask >> @splat(4));
                    return @bitCast(shift_trunc);
                }
            });

            fn MatchVector(comptime Reducer: type) type {
                return struct {
                    pub const shift = Reducer.shift;
                    pub const Input = @Vector(Reducer.vec_size, u8);
                    pub inline fn match(matcher: Matcher, input: Input) @TypeOf(Reducer.reduce(undefined)) {
                        const zero: Input = @splat(0);
                        const used: Input = @splat(@bitCast(Metadata{ .fingerprint = 0, .used = 1 }));

                        return Reducer.reduce(switch (matcher) {
                            .eq => |tag| input == @as(Input, @splat(@bitCast(tag))),
                            .used => input & used != zero,
                            .empty => input == zero,
                            .empty_or_tombstone => input & used == zero,
                        });
                    }
                };
            }

            /// For platforms without any efficient vector support. Uses bit tricks to match a byte in a usize.
            const MatchScalar = struct {
                pub const shift = 3;
                pub const Input = usize;
                pub inline fn match(matcher: Matcher, input: Input) usize {
                    // The hi bit also represents a used Metadata slot.
                    const lo: usize = @bitCast([_]u8{0x01} ** lanes);
                    const hi: usize = @bitCast([_]u8{0x80} ** lanes);
                    comptime assert(@as(u8, @truncate(hi)) == @as(u8, @bitCast(Metadata{ .fingerprint = 0, .used = 1 })));

                    return switch (matcher) {
                        // https://graphics.stanford.edu/~seander/bithacks.html##ValueInWord
                        .eq => |tag| match(.empty, input ^ (lo *% @as(u8, @bitCast(tag)))),
                        // The hi mask also acts as a Metadata.used mask,
                        .used => input & hi,
                        // https://graphics.stanford.edu/~seander/bithacks.html#ZeroInWord
                        .empty => (input -% lo) & ~input & hi,
                        // Opposite of .used
                        .empty_or_tombstone => ~input & hi,
                    };
                }
            };
        };

        pub const Iterator = struct {
            hm: ?*const Self,
            idx: Size = 0,
            mask: Scan.Mask = 0,

            pub fn next(it: *Iterator) ?Entry {
                const hm = it.hm orelse return null;
                while (it.mask == 0) {
                    if (it.idx >= hm.capacity()) {
                        it.hm = null;
                        return null;
                    }
                    it.mask = Scan.match(.used, Scan.read(hm.metadata.? + it.idx));
                    it.idx += Scan.lanes;
                }
                const idx = (it.idx + (@ctz(it.mask) >> Scan.shift)) - Scan.lanes;
                it.mask &= it.mask - 1;
                return Entry{
                    .key_ptr = &hm.keys()[idx],
                    .value_ptr = &hm.values()[idx],
                };
            }
        };

        pub const KeyIterator = FieldIterator(K);
        pub const ValueIterator = FieldIterator(V);

        fn FieldIterator(comptime T: type) type {
            return struct {
                metadata: [*]Metadata,
                items: [*]T,
                limit: Size,
                mask: Scan.Mask = 0,

                pub fn next(it: *@This()) ?*T {
                    while (it.mask == 0) {
                        it.limit = std.math.sub(Size, it.limit, Scan.lanes) catch return null;
                        it.mask = Scan.match(.used, Scan.read(it.metadata));
                        it.metadata += Scan.lanes;
                        it.items += Scan.lanes;
                    }
                    const item = (it.items + (@ctz(it.mask) >> Scan.shift)) - Scan.lanes;
                    it.mask &= it.mask - 1;
                    return &item[0];
                }
            };
        }

        pub const GetOrPutResult = struct {
            key_ptr: *K,
            value_ptr: *V,
            found_existing: bool,
        };

        pub const Managed = HashMap(K, V, Context, max_load_percentage);

        pub fn promote(self: Self, allocator: Allocator) Managed {
            if (@sizeOf(Context) != 0)
                @compileError("Cannot infer context " ++ @typeName(Context) ++ ", call promoteContext instead.");
            return promoteContext(self, allocator, undefined);
        }

        pub fn promoteContext(self: Self, allocator: Allocator, ctx: Context) Managed {
            return .{
                .unmanaged = self,
                .allocator = allocator,
                .ctx = ctx,
            };
        }

        fn isUnderMaxLoadPercentage(size: Size, cap: Size) bool {
            return size * 100 < max_load_percentage * cap;
        }

        pub fn deinit(self: *Self, allocator: Allocator) void {
            self.deallocate(allocator);
            self.* = undefined;
        }

        fn capacityForSize(size: Size) Size {
            var new_cap: u32 = @truncate((@as(u64, size) * 100) / max_load_percentage + 1);
            new_cap = math.ceilPowerOfTwo(u32, new_cap) catch unreachable;
            return new_cap;
        }

        pub fn ensureTotalCapacity(self: *Self, allocator: Allocator, new_size: Size) Allocator.Error!void {
            if (@sizeOf(Context) != 0)
                @compileError("Cannot infer context " ++ @typeName(Context) ++ ", call ensureTotalCapacityContext instead.");
            return ensureTotalCapacityContext(self, allocator, new_size, undefined);
        }
        pub fn ensureTotalCapacityContext(self: *Self, allocator: Allocator, new_size: Size, ctx: Context) Allocator.Error!void {
            if (new_size > self.size)
                try self.growIfNeeded(allocator, new_size - self.size, ctx);
        }

        pub fn ensureUnusedCapacity(self: *Self, allocator: Allocator, additional_size: Size) Allocator.Error!void {
            if (@sizeOf(Context) != 0)
                @compileError("Cannot infer context " ++ @typeName(Context) ++ ", call ensureUnusedCapacityContext instead.");
            return ensureUnusedCapacityContext(self, allocator, additional_size, undefined);
        }
        pub fn ensureUnusedCapacityContext(self: *Self, allocator: Allocator, additional_size: Size, ctx: Context) Allocator.Error!void {
            return ensureTotalCapacityContext(self, allocator, self.count() + additional_size, ctx);
        }

        pub fn clearRetainingCapacity(self: *Self) void {
            const metadata = self.metadata orelse return;
            const meta_lanes = @max(1, self.capacity() / Scan.lanes) * Scan.lanes;
            @memset(metadata[0..meta_lanes], Metadata.empty);

            self.size = 0;
            self.available = @as(u32, @truncate((self.capacity() * max_load_percentage) / 100));
        }

        pub fn clearAndFree(self: *Self, allocator: Allocator) void {
            self.deallocate(allocator);
        }

        pub fn count(self: *const Self) Size {
            return self.size;
        }

        fn header(self: *const Self) *Header {
            return @ptrCast(@as([*]Header, @ptrCast(@alignCast(self.metadata.?))) - 1);
        }

        fn keys(self: *const Self) [*]K {
            return self.header().keys;
        }

        fn values(self: *const Self) [*]V {
            return self.header().values;
        }

        pub fn capacity(self: *const Self) Size {
            if (self.metadata == null) return 0;

            return self.header().capacity;
        }

        pub fn iterator(self: *const Self) Iterator {
            return .{ .hm = if (self.count() > 0) self else null };
        }

        pub fn keyIterator(self: *const Self) KeyIterator {
            if (self.metadata) |metadata| {
                return .{
                    .metadata = metadata,
                    .items = self.keys(),
                    .limit = self.capacity(),
                };
            } else {
                return .{
                    .metadata = undefined,
                    .items = undefined,
                    .limit = 0,
                };
            }
        }

        pub fn valueIterator(self: *const Self) ValueIterator {
            if (self.metadata) |metadata| {
                return .{
                    .metadata = metadata,
                    .items = self.values(),
                    .limit = self.capacity(),
                };
            } else {
                return .{
                    .metadata = undefined,
                    .items = undefined,
                    .limit = 0,
                };
            }
        }

        /// Insert an entry in the map. Assumes it is not already present.
        pub fn putNoClobber(self: *Self, allocator: Allocator, key: K, value: V) Allocator.Error!void {
            if (@sizeOf(Context) != 0)
                @compileError("Cannot infer context " ++ @typeName(Context) ++ ", call putNoClobberContext instead.");
            return self.putNoClobberContext(allocator, key, value, undefined);
        }
        pub fn putNoClobberContext(self: *Self, allocator: Allocator, key: K, value: V, ctx: Context) Allocator.Error!void {
            assert(!self.containsContext(key, ctx));
            try self.growIfNeeded(allocator, 1, ctx);

            self.putAssumeCapacityNoClobberContext(key, value, ctx);
        }

        /// Asserts there is enough capacity to store the new key-value pair.
        /// Clobbers any existing data. To detect if a put would clobber
        /// existing data, see `getOrPutAssumeCapacity`.
        pub fn putAssumeCapacity(self: *Self, key: K, value: V) void {
            if (@sizeOf(Context) != 0)
                @compileError("Cannot infer context " ++ @typeName(Context) ++ ", call putAssumeCapacityContext instead.");
            return self.putAssumeCapacityContext(key, value, undefined);
        }
        pub fn putAssumeCapacityContext(self: *Self, key: K, value: V, ctx: Context) void {
            const gop = self.getOrPutAssumeCapacityContext(key, ctx);
            gop.value_ptr.* = value;
        }

        /// Insert an entry in the map. Assumes it is not already present,
        /// and that no allocation is needed.
        pub fn putAssumeCapacityNoClobber(self: *Self, key: K, value: V) void {
            if (@sizeOf(Context) != 0)
                @compileError("Cannot infer context " ++ @typeName(Context) ++ ", call putAssumeCapacityNoClobberContext instead.");
            return self.putAssumeCapacityNoClobberContext(key, value, undefined);
        }
        pub fn putAssumeCapacityNoClobberContext(self: *Self, key: K, value: V, ctx: Context) void {
            assert(!self.containsContext(key, ctx));

            const hash = ctx.hash(key);
            const mask = self.capacity() - 1;
            var pos = @as(usize, @truncate(hash & mask));

            const idx = while (true) {
                const chunk = (pos / Scan.lanes) * Scan.lanes;
                pos = (pos + Scan.lanes) & mask;

                const unused = Scan.match(.empty_or_tombstone, Scan.read(self.metadata.? + chunk));
                const idx = chunk + (@ctz(unused) >> Scan.shift);
                if (unused != 0) break idx;
            };

            self.metadata.?[idx] = Metadata.takeFingerprint(hash);
            self.keys()[idx] = key;
            self.values()[idx] = value;

            assert(self.available > 0);
            self.available -= 1;
            self.size += 1;
        }

        /// Inserts a new `Entry` into the hash map, returning the previous one, if any.
        pub fn fetchPut(self: *Self, allocator: Allocator, key: K, value: V) Allocator.Error!?KV {
            if (@sizeOf(Context) != 0)
                @compileError("Cannot infer context " ++ @typeName(Context) ++ ", call fetchPutContext instead.");
            return self.fetchPutContext(allocator, key, value, undefined);
        }
        pub fn fetchPutContext(self: *Self, allocator: Allocator, key: K, value: V, ctx: Context) Allocator.Error!?KV {
            const gop = try self.getOrPutContext(allocator, key, ctx);
            var result: ?KV = null;
            if (gop.found_existing) {
                result = KV{
                    .key = gop.key_ptr.*,
                    .value = gop.value_ptr.*,
                };
            }
            gop.value_ptr.* = value;
            return result;
        }

        /// Inserts a new `Entry` into the hash map, returning the previous one, if any.
        /// If insertion happens, asserts there is enough capacity without allocating.
        pub fn fetchPutAssumeCapacity(self: *Self, key: K, value: V) ?KV {
            if (@sizeOf(Context) != 0)
                @compileError("Cannot infer context " ++ @typeName(Context) ++ ", call fetchPutAssumeCapacityContext instead.");
            return self.fetchPutAssumeCapacityContext(key, value, undefined);
        }
        pub fn fetchPutAssumeCapacityContext(self: *Self, key: K, value: V, ctx: Context) ?KV {
            const gop = self.getOrPutAssumeCapacityContext(key, ctx);
            var result: ?KV = null;
            if (gop.found_existing) {
                result = KV{
                    .key = gop.key_ptr.*,
                    .value = gop.value_ptr.*,
                };
            }
            gop.value_ptr.* = value;
            return result;
        }

        /// If there is an `Entry` with a matching key, it is deleted from
        /// the hash map, and then returned from this function.
        pub fn fetchRemove(self: *Self, key: K) ?KV {
            if (@sizeOf(Context) != 0)
                @compileError("Cannot infer context " ++ @typeName(Context) ++ ", call fetchRemoveContext instead.");
            return self.fetchRemoveContext(key, undefined);
        }
        pub fn fetchRemoveContext(self: *Self, key: K, ctx: Context) ?KV {
            return self.fetchRemoveAdapted(key, ctx);
        }
        pub fn fetchRemoveAdapted(self: *Self, key: anytype, ctx: anytype) ?KV {
            if (self.getIndex(key, ctx)) |idx| {
                const old_key = &self.keys()[idx];
                const old_val = &self.values()[idx];
                const result = KV{
                    .key = old_key.*,
                    .value = old_val.*,
                };
                self.metadata.?[idx] = Metadata.tombstone;
                old_key.* = undefined;
                old_val.* = undefined;
                self.size -= 1;
                self.available += 1;
                return result;
            }

            return null;
        }

        /// Find the index containing the data for the given key.
        /// Whether this function returns null is almost always
        /// branched on after this function returns, and this function
        /// returns null/not null from separate code paths.  We
        /// want the optimizer to remove that branch and instead directly
        /// fuse the basic blocks after the branch to the basic blocks
        /// from this function.  To encourage that, this function is
        /// marked as inline.
        inline fn getIndex(self: Self, key: anytype, ctx: anytype) ?usize {
            comptime verifyContext(@TypeOf(ctx), @TypeOf(key), K, Hash, false);

            if (self.size == 0) {
                return null;
            }

            const hash = ctx.hash(key);
            if (@TypeOf(hash) != Hash) {
                @compileError("Context " ++ @typeName(@TypeOf(ctx)) ++ " has a generic hash function that returns the wrong type! " ++ @typeName(Hash) ++ " was expected, but found " ++ @typeName(@TypeOf(hash)));
            }

            const mask = self.capacity() - 1;
            const tag = Metadata.takeFingerprint(hash);
            var limit = mask;
            var pos = @as(usize, @truncate(hash & mask));

            while (true) {
                const chunk = (pos / Scan.lanes) * Scan.lanes;
                const input = Scan.read(self.metadata.? + chunk);
                pos = (pos + Scan.lanes) & mask;

                var matches = Scan.match(.{ .eq = tag }, input);
                while (matches != 0) : (matches &= matches - 1) {
                    const idx = chunk + (@ctz(matches) >> Scan.shift);
                    const eql = ctx.eql(key, self.keys()[idx]);
                    if (@TypeOf(eql) != bool) {
                        @compileError("Context " ++ @typeName(@TypeOf(ctx)) ++ " has a generic eql function that returns the wrong type! bool was expected, but found " ++ @typeName(@TypeOf(eql)));
                    }
                    if (eql) {
                        return idx;
                    }
                }

                limit = std.math.sub(Size, limit, Scan.lanes) catch break;
                if (Scan.match(.empty, input) != 0) {
                    break;
                }
            }

            return null;
        }

        pub fn getEntry(self: Self, key: K) ?Entry {
            if (@sizeOf(Context) != 0)
                @compileError("Cannot infer context " ++ @typeName(Context) ++ ", call getEntryContext instead.");
            return self.getEntryContext(key, undefined);
        }
        pub fn getEntryContext(self: Self, key: K, ctx: Context) ?Entry {
            return self.getEntryAdapted(key, ctx);
        }
        pub fn getEntryAdapted(self: Self, key: anytype, ctx: anytype) ?Entry {
            if (self.getIndex(key, ctx)) |idx| {
                return Entry{
                    .key_ptr = &self.keys()[idx],
                    .value_ptr = &self.values()[idx],
                };
            }
            return null;
        }

        /// Insert an entry if the associated key is not already present, otherwise update preexisting value.
        pub fn put(self: *Self, allocator: Allocator, key: K, value: V) Allocator.Error!void {
            if (@sizeOf(Context) != 0)
                @compileError("Cannot infer context " ++ @typeName(Context) ++ ", call putContext instead.");
            return self.putContext(allocator, key, value, undefined);
        }
        pub fn putContext(self: *Self, allocator: Allocator, key: K, value: V, ctx: Context) Allocator.Error!void {
            const result = try self.getOrPutContext(allocator, key, ctx);
            result.value_ptr.* = value;
        }

        /// Get an optional pointer to the actual key associated with adapted key, if present.
        pub fn getKeyPtr(self: Self, key: K) ?*K {
            if (@sizeOf(Context) != 0)
                @compileError("Cannot infer context " ++ @typeName(Context) ++ ", call getKeyPtrContext instead.");
            return self.getKeyPtrContext(key, undefined);
        }
        pub fn getKeyPtrContext(self: Self, key: K, ctx: Context) ?*K {
            return self.getKeyPtrAdapted(key, ctx);
        }
        pub fn getKeyPtrAdapted(self: Self, key: anytype, ctx: anytype) ?*K {
            if (self.getIndex(key, ctx)) |idx| {
                return &self.keys()[idx];
            }
            return null;
        }

        /// Get a copy of the actual key associated with adapted key, if present.
        pub fn getKey(self: Self, key: K) ?K {
            if (@sizeOf(Context) != 0)
                @compileError("Cannot infer context " ++ @typeName(Context) ++ ", call getKeyContext instead.");
            return self.getKeyContext(key, undefined);
        }
        pub fn getKeyContext(self: Self, key: K, ctx: Context) ?K {
            return self.getKeyAdapted(key, ctx);
        }
        pub fn getKeyAdapted(self: Self, key: anytype, ctx: anytype) ?K {
            if (self.getIndex(key, ctx)) |idx| {
                return self.keys()[idx];
            }
            return null;
        }

        /// Get an optional pointer to the value associated with key, if present.
        pub fn getPtr(self: Self, key: K) ?*V {
            if (@sizeOf(Context) != 0)
                @compileError("Cannot infer context " ++ @typeName(Context) ++ ", call getPtrContext instead.");
            return self.getPtrContext(key, undefined);
        }
        pub fn getPtrContext(self: Self, key: K, ctx: Context) ?*V {
            return self.getPtrAdapted(key, ctx);
        }
        pub fn getPtrAdapted(self: Self, key: anytype, ctx: anytype) ?*V {
            if (self.getIndex(key, ctx)) |idx| {
                return &self.values()[idx];
            }
            return null;
        }

        /// Get a copy of the value associated with key, if present.
        pub fn get(self: Self, key: K) ?V {
            if (@sizeOf(Context) != 0)
                @compileError("Cannot infer context " ++ @typeName(Context) ++ ", call getContext instead.");
            return self.getContext(key, undefined);
        }
        pub fn getContext(self: Self, key: K, ctx: Context) ?V {
            return self.getAdapted(key, ctx);
        }
        pub fn getAdapted(self: Self, key: anytype, ctx: anytype) ?V {
            if (self.getIndex(key, ctx)) |idx| {
                return self.values()[idx];
            }
            return null;
        }

        pub fn getOrPut(self: *Self, allocator: Allocator, key: K) Allocator.Error!GetOrPutResult {
            if (@sizeOf(Context) != 0)
                @compileError("Cannot infer context " ++ @typeName(Context) ++ ", call getOrPutContext instead.");
            return self.getOrPutContext(allocator, key, undefined);
        }
        pub fn getOrPutContext(self: *Self, allocator: Allocator, key: K, ctx: Context) Allocator.Error!GetOrPutResult {
            const gop = try self.getOrPutContextAdapted(allocator, key, ctx, ctx);
            if (!gop.found_existing) {
                gop.key_ptr.* = key;
            }
            return gop;
        }
        pub fn getOrPutAdapted(self: *Self, allocator: Allocator, key: anytype, key_ctx: anytype) Allocator.Error!GetOrPutResult {
            if (@sizeOf(Context) != 0)
                @compileError("Cannot infer context " ++ @typeName(Context) ++ ", call getOrPutContextAdapted instead.");
            return self.getOrPutContextAdapted(allocator, key, key_ctx, undefined);
        }
        pub fn getOrPutContextAdapted(self: *Self, allocator: Allocator, key: anytype, key_ctx: anytype, ctx: Context) Allocator.Error!GetOrPutResult {
            self.growIfNeeded(allocator, 1, ctx) catch |err| {
                // If allocation fails, try to do the lookup anyway.
                // If we find an existing item, we can return it.
                // Otherwise return the error, we could not add another.
                const index = self.getIndex(key, key_ctx) orelse return err;
                return GetOrPutResult{
                    .key_ptr = &self.keys()[index],
                    .value_ptr = &self.values()[index],
                    .found_existing = true,
                };
            };
            return self.getOrPutAssumeCapacityAdapted(key, key_ctx);
        }

        pub fn getOrPutAssumeCapacity(self: *Self, key: K) GetOrPutResult {
            if (@sizeOf(Context) != 0)
                @compileError("Cannot infer context " ++ @typeName(Context) ++ ", call getOrPutAssumeCapacityContext instead.");
            return self.getOrPutAssumeCapacityContext(key, undefined);
        }
        pub fn getOrPutAssumeCapacityContext(self: *Self, key: K, ctx: Context) GetOrPutResult {
            const result = self.getOrPutAssumeCapacityAdapted(key, ctx);
            if (!result.found_existing) {
                result.key_ptr.* = key;
            }
            return result;
        }
        pub fn getOrPutAssumeCapacityAdapted(self: *Self, key: anytype, ctx: anytype) GetOrPutResult {
            comptime verifyContext(@TypeOf(ctx), @TypeOf(key), K, Hash, false);

            const hash = ctx.hash(key);
            if (@TypeOf(hash) != Hash) {
                @compileError("Context " ++ @typeName(@TypeOf(ctx)) ++ " has a generic hash function that returns the wrong type! " ++ @typeName(Hash) ++ " was expected, but found " ++ @typeName(@TypeOf(hash)));
            }

            const mask = self.capacity() - 1;
            const tag = Metadata.takeFingerprint(hash);
            var limit = mask;
            var new_idx: usize = 0;
            var pos: usize = @truncate(hash & mask);

            while (true) {
                const chunk = (pos / Scan.lanes) * Scan.lanes;
                const input = Scan.read(self.metadata.? + chunk);
                pos = (pos + Scan.lanes) & mask;

                var matches = Scan.match(.{ .eq = tag }, input);
                while (matches != 0) : (matches &= matches - 1) {
                    const idx = chunk + (@ctz(matches) >> Scan.shift);
                    const key_ptr = &self.keys()[idx];
                    const value_ptr = &self.values()[idx];

                    const eql = ctx.eql(key, key_ptr.*);
                    if (@TypeOf(eql) != bool) {
                        @compileError("Context " ++ @typeName(@TypeOf(ctx)) ++ " has a generic eql function that returns the wrong type! bool was expected, but found " ++ @typeName(@TypeOf(eql)));
                    }

                    if (eql) {
                        return GetOrPutResult{
                            .key_ptr = key_ptr,
                            .value_ptr = value_ptr,
                            .found_existing = true,
                        };
                    }
                }

                if (new_idx == 0) {
                    const unused = Scan.match(.empty_or_tombstone, input);
                    new_idx = (chunk + (@ctz(unused) >> Scan.shift) + 1) * @intFromBool(unused != 0);
                }

                limit = std.math.sub(Size, limit, Scan.lanes) catch break;
                if (Scan.match(.empty, input) != 0) {
                    break;
                }
            }

            const idx = new_idx - 1;
            self.metadata.?[idx] = tag;
            self.available -= 1;
            self.size += 1;

            const key_ptr = &self.keys()[idx];
            const value_ptr = &self.values()[idx];
            key_ptr.* = undefined;
            value_ptr.* = undefined;

            return GetOrPutResult{
                .key_ptr = key_ptr,
                .value_ptr = value_ptr,
                .found_existing = false,
            };
        }

        pub fn getOrPutValue(self: *Self, allocator: Allocator, key: K, value: V) Allocator.Error!Entry {
            if (@sizeOf(Context) != 0)
                @compileError("Cannot infer context " ++ @typeName(Context) ++ ", call getOrPutValueContext instead.");
            return self.getOrPutValueContext(allocator, key, value, undefined);
        }
        pub fn getOrPutValueContext(self: *Self, allocator: Allocator, key: K, value: V, ctx: Context) Allocator.Error!Entry {
            const res = try self.getOrPutAdapted(allocator, key, ctx);
            if (!res.found_existing) {
                res.key_ptr.* = key;
                res.value_ptr.* = value;
            }
            return Entry{ .key_ptr = res.key_ptr, .value_ptr = res.value_ptr };
        }

        /// Return true if there is a value associated with key in the map.
        pub fn contains(self: *const Self, key: K) bool {
            if (@sizeOf(Context) != 0)
                @compileError("Cannot infer context " ++ @typeName(Context) ++ ", call containsContext instead.");
            return self.containsContext(key, undefined);
        }
        pub fn containsContext(self: *const Self, key: K, ctx: Context) bool {
            return self.containsAdapted(key, ctx);
        }
        pub fn containsAdapted(self: *const Self, key: anytype, ctx: anytype) bool {
            return self.getIndex(key, ctx) != null;
        }

        fn removeByIndex(self: *Self, idx: usize) void {
            self.metadata.?[idx] = Metadata.tombstone;
            self.keys()[idx] = undefined;
            self.values()[idx] = undefined;
            self.size -= 1;
            self.available += 1;
        }

        /// If there is an `Entry` with a matching key, it is deleted from
        /// the hash map, and this function returns true.  Otherwise this
        /// function returns false.
        pub fn remove(self: *Self, key: K) bool {
            if (@sizeOf(Context) != 0)
                @compileError("Cannot infer context " ++ @typeName(Context) ++ ", call removeContext instead.");
            return self.removeContext(key, undefined);
        }
        pub fn removeContext(self: *Self, key: K, ctx: Context) bool {
            return self.removeAdapted(key, ctx);
        }
        pub fn removeAdapted(self: *Self, key: anytype, ctx: anytype) bool {
            if (self.getIndex(key, ctx)) |idx| {
                self.removeByIndex(idx);
                return true;
            }

            return false;
        }

        /// Delete the entry with key pointed to by key_ptr from the hash map.
        /// key_ptr is assumed to be a valid pointer to a key that is present
        /// in the hash map.
        pub fn removeByPtr(self: *Self, key_ptr: *K) void {
            // TODO: replace with pointer subtraction once supported by zig
            // if @sizeOf(K) == 0 then there is at most one item in the hash
            // map, which is assumed to exist as key_ptr must be valid.  This
            // item must be at index 0.
            const idx = if (@sizeOf(K) > 0)
                (@intFromPtr(key_ptr) - @intFromPtr(self.keys())) / @sizeOf(K)
            else
                0;

            self.removeByIndex(idx);
        }

        // This counts the number of occupied slots (not counting tombstones), which is
        // what has to stay under the max_load_percentage of capacity.
        fn load(self: *const Self) Size {
            const max_load = (self.capacity() * max_load_percentage) / 100;
            assert(max_load >= self.available);
            return @as(Size, @truncate(max_load - self.available));
        }

        fn growIfNeeded(self: *Self, allocator: Allocator, new_count: Size, ctx: Context) Allocator.Error!void {
            if (new_count > self.available) {
                try self.grow(allocator, capacityForSize(self.load() + new_count), ctx);
            }
        }

        pub fn clone(self: Self, allocator: Allocator) Allocator.Error!Self {
            if (@sizeOf(Context) != 0)
                @compileError("Cannot infer context " ++ @typeName(Context) ++ ", call cloneContext instead.");
            return self.cloneContext(allocator, @as(Context, undefined));
        }
        pub fn cloneContext(self: Self, allocator: Allocator, new_ctx: anytype) Allocator.Error!HashMapUnmanaged(K, V, @TypeOf(new_ctx), max_load_percentage) {
            var other = HashMapUnmanaged(K, V, @TypeOf(new_ctx), max_load_percentage){};

            if (self.size > 0) {
                try other.allocate(allocator, capacityForSize(self.size));
                self.rehashContext(&other, new_ctx);
            }

            return other;
        }

        fn rehashContext(self: Self, other: anytype, ctx: anytype) void {
            const metadata = self.metadata.?;
            const keys_ptr = self.keys();
            const values_ptr = self.values();

            defer assert(self.size == other.size);

            var pos_idx: usize = 0;
            var limit = self.capacity() - 1;
            while (true) {
                var used = Scan.match(.used, Scan.read(metadata + pos_idx));
                while (used != 0) : (used &= used - 1) {
                    const idx = pos_idx + (@ctz(used) >> Scan.shift);
                    other.putAssumeCapacityNoClobberContext(keys_ptr[idx], values_ptr[idx], ctx);
                    if (other.size == self.size) {
                        return;
                    }
                }

                pos_idx += Scan.lanes;
                limit = std.math.sub(Size, limit, Scan.lanes) catch return;
            }
        }

        /// Set the map to an empty state, making deinitialization a no-op, and
        /// returning a copy of the original.
        pub fn move(self: *Self) Self {
            const result = self.*;
            self.* = .{};
            return result;
        }

        fn grow(self: *Self, allocator: Allocator, new_capacity: Size, ctx: Context) Allocator.Error!void {
            @setCold(true);
            const new_cap = @max(new_capacity, minimal_capacity);
            assert(new_cap > self.capacity());
            assert(std.math.isPowerOfTwo(new_cap));

            var map = Self{};
            defer map.deinit(allocator);
            try map.allocate(allocator, new_cap);

            if (self.size > 0) {
                self.rehashContext(&map, ctx);
            }

            std.mem.swap(Self, self, &map);
        }

        fn allocate(self: *Self, allocator: Allocator, new_capacity: Size) Allocator.Error!void {
            const meta_lanes = @max(1, new_capacity / Scan.lanes) * Scan.lanes;
            const meta_size = @sizeOf(Header) + meta_lanes * @sizeOf(Metadata);
            comptime assert(@alignOf(Metadata) == 1);

            const keys_start = std.mem.alignForward(usize, meta_size, @alignOf(K));
            const keys_end = keys_start + new_capacity * @sizeOf(K);

            const vals_start = std.mem.alignForward(usize, keys_end, @alignOf(V));
            const vals_end = vals_start + new_capacity * @sizeOf(V);

            const max_align = comptime @max(@alignOf(Header), @alignOf(K), @alignOf(V));
            const bytes = try allocator.alignedAlloc(u8, max_align, vals_end);

            @as(*Header, @ptrCast(bytes.ptr)).* = .{
                .keys = @ptrCast(@alignCast(bytes.ptr + keys_start)),
                .values = @ptrCast(@alignCast(bytes.ptr + vals_start)),
                .capacity = new_capacity,
            };

            self.metadata = @ptrCast(bytes.ptr + @sizeOf(Header));
            self.clearRetainingCapacity();
        }

        fn deallocate(self: *Self, allocator: Allocator) void {
            const metadata = self.metadata orelse return;
            const header_ptr: *Header = @ptrCast(@alignCast(metadata - @sizeOf(Header)));
            self.* = .{};

            const meta_lanes = @max(1, header_ptr.capacity / Scan.lanes) * Scan.lanes;
            const meta_size = @sizeOf(Header) + meta_lanes * @sizeOf(Metadata);

            const keys_start = std.mem.alignForward(usize, meta_size, @alignOf(K));
            const keys_end = keys_start + header_ptr.capacity * @sizeOf(K);

            const vals_start = std.mem.alignForward(usize, keys_end, @alignOf(V));
            const vals_end = vals_start + header_ptr.capacity * @sizeOf(V);

            const max_align = comptime @max(@alignOf(Header), @alignOf(K), @alignOf(V));
            const bytes: [*]align(max_align) u8 = @ptrCast(@alignCast(header_ptr));
            allocator.free(bytes[0..vals_end]);
        }

        /// This function is used in the debugger pretty formatters in tools/ to fetch the
        /// header type to facilitate fancy debug printing for this type.
        fn dbHelper(self: *Self, hdr: *Header, entry: *Entry) void {
            _ = self;
            _ = hdr;
            _ = entry;
        }

        comptime {
            if (builtin.mode == .Debug) {
                _ = &dbHelper;
            }
        }
    };
}

const testing = std.testing;
const expect = std.testing.expect;
const expectEqual = std.testing.expectEqual;

test "std.hash_map basic usage" {
    var map = AutoHashMap(u32, u32).init(std.testing.allocator);
    defer map.deinit();

    const count = 5;
    var i: u32 = 0;
    var total: u32 = 0;
    while (i < count) : (i += 1) {
        try map.put(i, i);
        total += i;
    }

    var sum: u32 = 0;
    var it = map.iterator();
    while (it.next()) |kv| {
        sum += kv.key_ptr.*;
    }
    try expectEqual(total, sum);

    i = 0;
    sum = 0;
    while (i < count) : (i += 1) {
        try expectEqual(i, map.get(i).?);
        sum += map.get(i).?;
    }
    try expectEqual(total, sum);
}

test "std.hash_map ensureTotalCapacity" {
    var map = AutoHashMap(i32, i32).init(std.testing.allocator);
    defer map.deinit();

    try map.ensureTotalCapacity(20);
    const initial_capacity = map.capacity();
    try testing.expect(initial_capacity >= 20);
    var i: i32 = 0;
    while (i < 20) : (i += 1) {
        try testing.expect(map.fetchPutAssumeCapacity(i, i + 10) == null);
    }
    // shouldn't resize from putAssumeCapacity
    try testing.expect(initial_capacity == map.capacity());
}

test "std.hash_map ensureUnusedCapacity with tombstones" {
    var map = AutoHashMap(i32, i32).init(std.testing.allocator);
    defer map.deinit();

    var i: i32 = 0;
    while (i < 100) : (i += 1) {
        try map.ensureUnusedCapacity(1);
        map.putAssumeCapacity(i, i);
        _ = map.remove(i);
    }
}

test "std.hash_map clearRetainingCapacity" {
    var map = AutoHashMap(u32, u32).init(std.testing.allocator);
    defer map.deinit();

    map.clearRetainingCapacity();

    try map.put(1, 1);
    try expectEqual(map.get(1).?, 1);
    try expectEqual(map.count(), 1);

    map.clearRetainingCapacity();
    map.putAssumeCapacity(1, 1);
    try expectEqual(map.get(1).?, 1);
    try expectEqual(map.count(), 1);

    const cap = map.capacity();
    try expect(cap > 0);

    map.clearRetainingCapacity();
    map.clearRetainingCapacity();
    try expectEqual(map.count(), 0);
    try expectEqual(map.capacity(), cap);
    try expect(!map.contains(1));
}

test "std.hash_map grow" {
    var map = AutoHashMap(u32, u32).init(std.testing.allocator);
    defer map.deinit();

    const growTo = 12456;

    var i: u32 = 0;
    while (i < growTo) : (i += 1) {
        try map.put(i, i);
    }
    try expectEqual(map.count(), growTo);

    i = 0;
    var it = map.iterator();
    while (it.next()) |kv| {
        try expectEqual(kv.key_ptr.*, kv.value_ptr.*);
        i += 1;
    }
    try expectEqual(i, growTo);

    i = 0;
    while (i < growTo) : (i += 1) {
        try expectEqual(map.get(i).?, i);
    }
}

test "std.hash_map clone" {
    var map = AutoHashMap(u32, u32).init(std.testing.allocator);
    defer map.deinit();

    var a = try map.clone();
    defer a.deinit();

    try expectEqual(a.count(), 0);

    try a.put(1, 1);
    try a.put(2, 2);
    try a.put(3, 3);

    var b = try a.clone();
    defer b.deinit();

    try expectEqual(b.count(), 3);
    try expectEqual(b.get(1).?, 1);
    try expectEqual(b.get(2).?, 2);
    try expectEqual(b.get(3).?, 3);

    var original = AutoHashMap(i32, i32).init(std.testing.allocator);
    defer original.deinit();

    var i: u8 = 0;
    while (i < 10) : (i += 1) {
        try original.putNoClobber(i, i * 10);
    }

    var copy = try original.clone();
    defer copy.deinit();

    i = 0;
    while (i < 10) : (i += 1) {
        try testing.expect(copy.get(i).? == i * 10);
    }
}

test "std.hash_map ensureTotalCapacity with existing elements" {
    var map = AutoHashMap(u32, u32).init(std.testing.allocator);
    defer map.deinit();

    try map.put(0, 0);
    try expectEqual(map.count(), 1);
    try expectEqual(map.capacity(), @TypeOf(map).Unmanaged.minimal_capacity);

    try map.ensureTotalCapacity(65);
    try expectEqual(map.count(), 1);
    try expectEqual(map.capacity(), 128);
}

test "std.hash_map ensureTotalCapacity satisfies max load factor" {
    var map = AutoHashMap(u32, u32).init(std.testing.allocator);
    defer map.deinit();

    try map.ensureTotalCapacity(127);
    try expectEqual(map.capacity(), 256);
}

test "std.hash_map remove" {
    var map = AutoHashMap(u32, u32).init(std.testing.allocator);
    defer map.deinit();

    var i: u32 = 0;
    while (i < 16) : (i += 1) {
        try map.put(i, i);
    }

    i = 0;
    while (i < 16) : (i += 1) {
        if (i % 3 == 0) {
            _ = map.remove(i);
        }
    }
    try expectEqual(map.count(), 10);
    var it = map.iterator();
    while (it.next()) |kv| {
        try expectEqual(kv.key_ptr.*, kv.value_ptr.*);
        try expect(kv.key_ptr.* % 3 != 0);
    }

    i = 0;
    while (i < 16) : (i += 1) {
        if (i % 3 == 0) {
            try expect(!map.contains(i));
        } else {
            try expectEqual(map.get(i).?, i);
        }
    }
}

test "std.hash_map reverse removes" {
    var map = AutoHashMap(u32, u32).init(std.testing.allocator);
    defer map.deinit();

    var i: u32 = 0;
    while (i < 16) : (i += 1) {
        try map.putNoClobber(i, i);
    }

    i = 16;
    while (i > 0) : (i -= 1) {
        _ = map.remove(i - 1);
        try expect(!map.contains(i - 1));
        var j: u32 = 0;
        while (j < i - 1) : (j += 1) {
            try expectEqual(map.get(j).?, j);
        }
    }

    try expectEqual(map.count(), 0);
}

test "std.hash_map multiple removes on same metadata" {
    var map = AutoHashMap(u32, u32).init(std.testing.allocator);
    defer map.deinit();

    var i: u32 = 0;
    while (i < 16) : (i += 1) {
        try map.put(i, i);
    }

    _ = map.remove(7);
    _ = map.remove(15);
    _ = map.remove(14);
    _ = map.remove(13);
    try expect(!map.contains(7));
    try expect(!map.contains(15));
    try expect(!map.contains(14));
    try expect(!map.contains(13));

    i = 0;
    while (i < 13) : (i += 1) {
        if (i == 7) {
            try expect(!map.contains(i));
        } else {
            try expectEqual(map.get(i).?, i);
        }
    }

    try map.put(15, 15);
    try map.put(13, 13);
    try map.put(14, 14);
    try map.put(7, 7);
    i = 0;
    while (i < 16) : (i += 1) {
        try expectEqual(map.get(i).?, i);
    }
}

test "std.hash_map put and remove loop in random order" {
    var map = AutoHashMap(u32, u32).init(std.testing.allocator);
    defer map.deinit();

    var keys = std.ArrayList(u32).init(std.testing.allocator);
    defer keys.deinit();

    const size = 32;
    const iterations = 100;

    var i: u32 = 0;
    while (i < size) : (i += 1) {
        try keys.append(i);
    }
    var prng = std.rand.DefaultPrng.init(0);
    const random = prng.random();

    while (i < iterations) : (i += 1) {
        random.shuffle(u32, keys.items);

        for (keys.items) |key| {
            try map.put(key, key);
        }
        try expectEqual(map.count(), size);

        for (keys.items) |key| {
            _ = map.remove(key);
        }
        try expectEqual(map.count(), 0);
    }
}

test "std.hash_map remove one million elements in random order" {
    const Map = AutoHashMap(u32, u32);
    const n = 1000 * 1000;
    var map = Map.init(std.heap.page_allocator);
    defer map.deinit();

    var keys = std.ArrayList(u32).init(std.heap.page_allocator);
    defer keys.deinit();

    var i: u32 = 0;
    while (i < n) : (i += 1) {
        keys.append(i) catch unreachable;
    }

    var prng = std.rand.DefaultPrng.init(0);
    const random = prng.random();
    random.shuffle(u32, keys.items);

    for (keys.items) |key| {
        map.put(key, key) catch unreachable;
    }

    random.shuffle(u32, keys.items);
    i = 0;
    while (i < n) : (i += 1) {
        const key = keys.items[i];
        _ = map.remove(key);
    }
}

test "std.hash_map put" {
    var map = AutoHashMap(u32, u32).init(std.testing.allocator);
    defer map.deinit();

    var i: u32 = 0;
    while (i < 16) : (i += 1) {
        try map.put(i, i);
    }

    i = 0;
    while (i < 16) : (i += 1) {
        try expectEqual(map.get(i).?, i);
    }

    i = 0;
    while (i < 16) : (i += 1) {
        try map.put(i, i * 16 + 1);
    }

    i = 0;
    while (i < 16) : (i += 1) {
        try expectEqual(map.get(i).?, i * 16 + 1);
    }
}

test "std.hash_map putAssumeCapacity" {
    var map = AutoHashMap(u32, u32).init(std.testing.allocator);
    defer map.deinit();

    try map.ensureTotalCapacity(20);
    var i: u32 = 0;
    while (i < 20) : (i += 1) {
        map.putAssumeCapacityNoClobber(i, i);
    }

    i = 0;
    var sum = i;
    while (i < 20) : (i += 1) {
        sum += map.getPtr(i).?.*;
    }
    try expectEqual(sum, 190);

    i = 0;
    while (i < 20) : (i += 1) {
        map.putAssumeCapacity(i, 1);
    }

    i = 0;
    sum = i;
    while (i < 20) : (i += 1) {
        sum += map.get(i).?;
    }
    try expectEqual(sum, 20);
}

test "std.hash_map repeat putAssumeCapacity/remove" {
    var map = AutoHashMap(u32, u32).init(std.testing.allocator);
    defer map.deinit();

    try map.ensureTotalCapacity(20);
    const limit = map.unmanaged.available;

    var i: u32 = 0;
    while (i < limit) : (i += 1) {
        map.putAssumeCapacityNoClobber(i, i);
    }

    // Repeatedly delete/insert an entry without resizing the map.
    // Put to different keys so entries don't land in the just-freed slot.
    i = 0;
    while (i < 10 * limit) : (i += 1) {
        try testing.expect(map.remove(i));
        if (i % 2 == 0) {
            map.putAssumeCapacityNoClobber(limit + i, i);
        } else {
            map.putAssumeCapacity(limit + i, i);
        }
    }

    i = 9 * limit;
    while (i < 10 * limit) : (i += 1) {
        try expectEqual(map.get(limit + i), i);
    }
    try expectEqual(map.unmanaged.available, 0);
    try expectEqual(map.unmanaged.count(), limit);
}

test "std.hash_map getOrPut" {
    var map = AutoHashMap(u32, u32).init(std.testing.allocator);
    defer map.deinit();

    var i: u32 = 0;
    while (i < 10) : (i += 1) {
        try map.put(i * 2, 2);
    }

    i = 0;
    while (i < 20) : (i += 1) {
        _ = try map.getOrPutValue(i, 1);
    }

    i = 0;
    var sum = i;
    while (i < 20) : (i += 1) {
        sum += map.get(i).?;
    }

    try expectEqual(sum, 30);
}

test "std.hash_map basic hash map usage" {
    var map = AutoHashMap(i32, i32).init(std.testing.allocator);
    defer map.deinit();

    try testing.expect((try map.fetchPut(1, 11)) == null);
    try testing.expect((try map.fetchPut(2, 22)) == null);
    try testing.expect((try map.fetchPut(3, 33)) == null);
    try testing.expect((try map.fetchPut(4, 44)) == null);

    try map.putNoClobber(5, 55);
    try testing.expect((try map.fetchPut(5, 66)).?.value == 55);
    try testing.expect((try map.fetchPut(5, 55)).?.value == 66);

    const gop1 = try map.getOrPut(5);
    try testing.expect(gop1.found_existing == true);
    try testing.expect(gop1.value_ptr.* == 55);
    gop1.value_ptr.* = 77;
    try testing.expect(map.getEntry(5).?.value_ptr.* == 77);

    const gop2 = try map.getOrPut(99);
    try testing.expect(gop2.found_existing == false);
    gop2.value_ptr.* = 42;
    try testing.expect(map.getEntry(99).?.value_ptr.* == 42);

    const gop3 = try map.getOrPutValue(5, 5);
    try testing.expect(gop3.value_ptr.* == 77);

    const gop4 = try map.getOrPutValue(100, 41);
    try testing.expect(gop4.value_ptr.* == 41);

    try testing.expect(map.contains(2));
    try testing.expect(map.getEntry(2).?.value_ptr.* == 22);
    try testing.expect(map.get(2).? == 22);

    const rmv1 = map.fetchRemove(2);
    try testing.expect(rmv1.?.key == 2);
    try testing.expect(rmv1.?.value == 22);
    try testing.expect(map.fetchRemove(2) == null);
    try testing.expect(map.remove(2) == false);
    try testing.expect(map.getEntry(2) == null);
    try testing.expect(map.get(2) == null);

    try testing.expect(map.remove(3) == true);
}

test "std.hash_map getOrPutAdapted" {
    const AdaptedContext = struct {
        fn eql(self: @This(), adapted_key: []const u8, test_key: u64) bool {
            _ = self;
            return std.fmt.parseInt(u64, adapted_key, 10) catch unreachable == test_key;
        }
        fn hash(self: @This(), adapted_key: []const u8) u64 {
            _ = self;
            const key = std.fmt.parseInt(u64, adapted_key, 10) catch unreachable;
            return (AutoContext(u64){}).hash(key);
        }
    };
    var map = AutoHashMap(u64, u64).init(testing.allocator);
    defer map.deinit();

    const keys = [_][]const u8{
        "1231",
        "4564",
        "7894",
        "1132",
        "65235",
        "95462",
        "0112305",
        "00658",
        "0",
        "2",
    };

    var real_keys: [keys.len]u64 = undefined;

    inline for (keys, 0..) |key_str, i| {
        const result = try map.getOrPutAdapted(key_str, AdaptedContext{});
        try testing.expect(!result.found_existing);
        real_keys[i] = std.fmt.parseInt(u64, key_str, 10) catch unreachable;
        result.key_ptr.* = real_keys[i];
        result.value_ptr.* = i * 2;
    }

    try testing.expectEqual(map.count(), keys.len);

    inline for (keys, 0..) |key_str, i| {
        const result = map.getOrPutAssumeCapacityAdapted(key_str, AdaptedContext{});
        try testing.expect(result.found_existing);
        try testing.expectEqual(real_keys[i], result.key_ptr.*);
        try testing.expectEqual(@as(u64, i) * 2, result.value_ptr.*);
        try testing.expectEqual(real_keys[i], map.getKeyAdapted(key_str, AdaptedContext{}).?);
    }
}

test "std.hash_map ensureUnusedCapacity" {
    var map = AutoHashMap(u64, u64).init(testing.allocator);
    defer map.deinit();

    try map.ensureUnusedCapacity(32);
    const capacity = map.capacity();
    try map.ensureUnusedCapacity(32);

    // Repeated ensureUnusedCapacity() calls with no insertions between
    // should not change the capacity.
    try testing.expectEqual(capacity, map.capacity());
}

test "std.hash_map removeByPtr" {
    var map = AutoHashMap(i32, u64).init(testing.allocator);
    defer map.deinit();

    var i: i32 = undefined;

    i = 0;
    while (i < 10) : (i += 1) {
        try map.put(i, 0);
    }

    try testing.expect(map.count() == 10);

    i = 0;
    while (i < 10) : (i += 1) {
        const key_ptr = map.getKeyPtr(i);
        try testing.expect(key_ptr != null);

        if (key_ptr) |ptr| {
            map.removeByPtr(ptr);
        }
    }

    try testing.expect(map.count() == 0);
}

test "std.hash_map removeByPtr 0 sized key" {
    var map = AutoHashMap(u0, u64).init(testing.allocator);
    defer map.deinit();

    try map.put(0, 0);

    try testing.expect(map.count() == 1);

    const key_ptr = map.getKeyPtr(0);
    try testing.expect(key_ptr != null);

    if (key_ptr) |ptr| {
        map.removeByPtr(ptr);
    }

    try testing.expect(map.count() == 0);
}

test "std.hash_map repeat fetchRemove" {
    var map = AutoHashMapUnmanaged(u64, void){};
    defer map.deinit(testing.allocator);

    try map.ensureTotalCapacity(testing.allocator, 4);

    map.putAssumeCapacity(0, {});
    map.putAssumeCapacity(1, {});
    map.putAssumeCapacity(2, {});
    map.putAssumeCapacity(3, {});

    // fetchRemove() should make slots available.
    var i: usize = 0;
    while (i < 10) : (i += 1) {
        try testing.expect(map.fetchRemove(3) != null);
        map.putAssumeCapacity(3, {});
    }

    try testing.expect(map.get(0) != null);
    try testing.expect(map.get(1) != null);
    try testing.expect(map.get(2) != null);
    try testing.expect(map.get(3) != null);
}