# Proviso standard library through phase 2

This file lists the standard library items that phases 1 and 2 implement (OPEN_QUESTIONS Q36, P3). Each item is written as its declaration without a body. From phase 4, `proviso sig std` serves the same information from the installed toolchain (REFERENCE §16), and this file goes away.

- **Source.** From slice 3.4, the toolchain reads these declarations from Proviso source in `crates/check/std/`, one file per module. It binds each declaration without a body to an operation it implements (OPEN_QUESTIONS P5). The sources hold the items here that the toolchain implements, without their contracts, which wait for the verifier. `Set` stays E0901, and the checker still implements `parse` and the conversions itself.
- **Phase 1** already has `System.stdout`, `Out.write_line` and `IoError`. Slice 3.1 adds `In.read_line` and the permissions of `Out` and `In`, and slice 3.5 adds `std.fs`, `System.fs` and `std.test`. Everything else here is phase 2.
- **Contracts.** An `ensures` clause is listed where the verifier will need it (phase 5). The other items get theirs when `sig` exists (phase 4, T11). The toolchain implements these items natively and trusts them to meet their contracts, so the v1 profile doesn't check std contracts at runtime.
- **Later phases.** `map`, `filter` and the other operations that take a closure that may fail need effect variables (§9.5), which arrive in slice 3.6. `File`, `Dir.sub`, `FakeClock`, `FakeNet` and `SeededRandom` are not yet scheduled (Q6, Q36).

## The prelude

These items need no `use` (REFERENCE §3).

```proviso
pub enum Option[T] {
    Some(value: T)
    None
}

pub enum Result[T, E] {
    Ok(value: T)
    Err(error: E)
}

/// What `cmp` returns, ordered `Less < Equal < Greater`.
pub enum Ordering derives(Eq, Ord, Hash, Show) {
    Less
    Equal
    Greater
}

/// How `to_int` rounds a `Float` that isn't a whole number. The names are IEEE 754's.
pub enum Rounding derives(Eq, Hash, Show) {
    TowardZero
    TowardNegative
    TowardPositive
    NearestEven
    NearestAway
}

pub interface Eq {
    fn eq(self, other: Self) -> Bool
}

pub interface Ord {
    fn cmp(self, other: Self) -> Ordering
}

pub interface Show {
    fn show(self) -> Text
}

/// Ends a resource on a failure exit (§10). Every resource type implements it.
pub interface Abandon {
    fn abandon(take self)
}
```

A hand-written `impl Ord` defines `cmp`. Then `<`, `<=`, `>` and `>=`, and the derived `Ord` of a type that holds the value, use it. `Float` and `Float32` have `<` but don't implement `Ord`.

`Hash` has no method that phase 2 code calls. It is only derived. `Copy` is satisfied automatically by copyable types with no reach (§5.1). `Index` is the built-in `xs[i]` and `pool[h]` below.

### Derived implementations

`derives(Eq, Ord, Hash, Show)` on a record, enum or distinct type generates these implementations:

| Interface | Behaviour |
|---|---|
| `Eq` | Equal when the variants are equal and every field is equal. |
| `Ord` | Compares variants in declaration order, then fields in declaration order. |
| `Hash` | Consistent with the derived `Eq`. |
| `Show` | Writes the expression that builds the value: `User(name: "ada", age: 36)`, `LoadError.MissingComma(line_no: 7)`, `Stop.Halt`, `UserId(7)`. Text and chars inside are quoted and escaped the way `debug` writes them (OPEN_QUESTIONS P5). |

`List`, `Map`, `Set`, `Option`, `Result` and tuples implement each of these interfaces when their element types do. `Show` writes them in literal form: `[1, 2]`, `["k": 1]`, `Some(3)`, `None`, `Ok("a")`, `(1, "a")`. A tuple is ordered element by element from the left.

### List

```proviso
impl[T] List[T] {
    /// The number of elements.
    pub fn len(self) -> Int
        ensures result >= 0

    pub fn is_empty(self) -> Bool
        ensures result == (self.len() == 0)

    /// Appends `value` at the end.
    pub fn push(inout self, value: take T)
        ensures self.len() == old(self.len()) + 1

    /// Removes the last element and returns it. The caller owns it (Q35). Returns `None` if the list is empty.
    pub fn pop(inout self) -> Option[T]
        ensures result is None or self.len() == old(self.len()) - 1
}

impl[T: Copy] List[T] {
    /// The element at `index`, or `None` if `index` is out of bounds.
    pub fn get(self, index: Int) -> Option[T]

    /// Each element with its index, starting at 0.
    pub fn enumerate(self) -> List[(Int, T)]
}

impl[T: Eq] List[T] {
    pub fn contains(self, value: T) -> Bool
}
```

`xs[i]` reads element `i`, which stays in the list, so it is borrowed. Copying it, by binding, returning or storing it, needs `T: Copy`, and a use that only borrows it, such as a method call on it, needs none (REFERENCE §4.8). An index out of bounds is an `index_out_of_bounds` defect. `xs[i] = v` replaces element `i`, under the same bounds check. If `T` is a resource, `xs[i] = v` is a compile error, because it would discard the old element (§10 rule 5).

### Map and Set

```proviso
impl[K: Eq + Hash, V] Map[K, V] {
    pub fn len(self) -> Int
        ensures result >= 0

    pub fn is_empty(self) -> Bool
        ensures result == (self.len() == 0)

    pub fn contains_key(self, key: K) -> Bool

    /// Maps `key` to `value`. Returns the value it replaces, so a resource is never discarded (§10 rule 5).
    pub fn set(inout self, key: take K, value: take V) -> Option[V]

    /// Removes `key` and returns its value, or `None` if `key` is absent.
    pub fn remove(inout self, key: K) -> Option[V]
}

impl[K: Eq + Hash, V: Copy] Map[K, V] {
    /// The value for `key`, or `None` if `key` is absent.
    pub fn get(self, key: K) -> Option[V]
}

impl[T: Eq + Hash] Set[T] {
    pub fn len(self) -> Int
        ensures result >= 0

    pub fn is_empty(self) -> Bool
        ensures result == (self.len() == 0)

    pub fn contains(self, value: T) -> Bool

    /// Adds `value`. Returns `false` if it was already present.
    pub fn insert(inout self, value: take T) -> Bool

    /// Removes `value`. Returns `false` if it was absent.
    pub fn remove(inout self, value: T) -> Bool
}
```

A `Map` or `Set` iterates in insertion order (§4.2).

### Text

```proviso
impl Text {
    /// The length of the UTF-8 encoding, in bytes.
    pub fn byte_len(self) -> Int
        ensures result >= 0

    pub fn is_empty(self) -> Bool
        ensures result == (self.byte_len() == 0)

    /// The text without leading and trailing Unicode `White_Space` characters.
    pub fn trim(self) -> Text

    /// The text before and after the first `sep`, or `None` if `sep` doesn't occur. An empty `sep` matches at the start.
    pub fn split_once(self, sep: Text) -> Option[(Text, Text)]

    /// The lines, without their `\n` or `\r\n` endings. A final line ending doesn't start an empty line.
    pub fn lines(self) -> List[Text]

    pub fn starts_with(self, prefix: Text) -> Bool

    /// The text after `prefix`, or `None` if the text doesn't start with it.
    pub fn strip_prefix(self, prefix: Text) -> Option[Text]
}
```

### Integers

```proviso
impl Int {
    /// Parses an optional `+` or `-` followed by one or more ASCII digits. Anything else fails, including whitespace and `_`.
    pub fn parse(text: Text) -> Int fails ParseError
}
```

Every integer type has the same `parse`. It fails with `ParseError.Empty` on empty text, with `ParseError.Invalid` on other text that isn't of that form, and with `ParseError.OutOfRange` when the value doesn't fit the type.

`derives` on a distinct type also takes `Add`, `Sub`, `Mul`, `Div` and `Neg` when the wrapped type has the operator, which then works on values of the distinct type (REFERENCE §4.6). These interfaces have no methods that phase 2 code calls or implements.

### Conversions

```proviso
impl Int32 {
    /// `value` as an `Int32`. Fails with `ConversionError.OutOfRange` when it doesn't fit.
    pub fn try_from(value: Int64) -> Int32 fails ConversionError

    /// The low 32 bits of `value`, as two's complement.
    pub fn wrapping_from(value: Int64) -> Int32
}

impl Float {
    /// The nearest `Float` to `value`, ties to even.
    pub fn from(value: Int64) -> Float

    /// `self` rounded to a whole number by `rounding`. Fails with `ConversionError.NotANumber` on NaN, and with `ConversionError.OutOfRange` when the result is infinite or doesn't fit an `Int`.
    pub fn to_int(self, rounding: Rounding) -> Int fails ConversionError
}
```

Every integer type has `try_from` and `wrapping_from`, and `Float` and `Float32` have `from` and `to_int`. `try_from`, `wrapping_from` and `from` each take a value of any integer type. Calling a numeric type as a function, as in `Int64(x)`, converts only when the target holds every value of the source type, as `Int64` holds every `Int32`, `Int16` every `UInt8`, `Float` every `Int32` and every `Float32`, and `Float32` every `UInt16`. Other conversions are a type error that names the function to use. `ConversionError` is in `std.num`.

## std.io

```proviso
/// A text output stream, such as `System.stdout` or `System.stderr`.
pub cap interface Out effects(write) {
    /// Writes `text` followed by a newline.
    fn write_line(self, text: Text) fails IoError                needs write
}

/// A text input stream, such as `System.stdin`.
pub cap interface In effects(read) {
    /// The next line, without its `\n` or `\r\n`, or `None` at the end of the input.
    fn read_line(self) -> Option[Text] fails IoError             needs read
}

/// An I/O failure. `show` gives the operating system's message.
pub opaque record IoError derives(Show)
```

Reading a line consumes it, so `read` is an `effects` permission (Q6). `System`'s `net`, `clock`, `random`, `env` and `process` fields have the types `Net[connect, listen]`, `Clock`, `Random`, `Env` and `Process[spawn]`, which no module exports yet and which have no operations yet. Their permissions are `effects` permissions (OPEN_QUESTIONS P5).

## std.fs

```proviso
/// A directory tree, such as `System.fs`, which the runtime roots at the run's working directory, or a fake from `std.test`.
pub cap interface Dir observes(read, list) effects(write, create, delete) {
    fn read_text(self, path: Path) -> Text fails FsError                   needs read

    /// Replaces the file's text, and creates the file if it is missing.
    fn write_text(self, path: Path, text: Text) fails FsError              needs write

    /// The file's length in bytes.
    fn size(self, path: Path) -> Int fails FsError                         needs read

    /// The directory's entries, ordered by the bytes of their names. Each is `path`, with `.` and `..` resolved, followed by `/` and the entry's name, or the name alone in the root.
    fn list(self, path: Path) -> List[Path] fails FsError                  needs list

    fn create_dir(self, path: Path) fails FsError                          needs create

    /// Removes a file or an empty directory.
    fn remove(self, path: Path) fails FsError                              needs delete
}

/// A path relative to a `Dir`'s root, with `/` between its parts.
pub type Path = distinct Text derives(Eq, Hash, Show)

/// Why an operation of a `Dir` failed.
pub enum FsError derives(Eq, Show) {
    NotFound(path: Path)
    PermissionDenied(path: Path)
    Other(message: Text)
}
```

`System.fs` is a `Dir[read, write, create, delete, list]` (§9.1). A path that is absolute, or whose `..` parts climb above the root, fails with `PermissionDenied`, and so does a symbolic link that leads out of the root (Q6, OPEN_QUESTIONS P5). `NotFound` and `PermissionDenied` hold the path as the call gave it. `Other` holds a message that says what is wrong with the path, such as that it is a directory. `Dir.sub` is not yet scheduled.

## std.test

```proviso
/// A directory tree in memory, for tests. Copies of it share its files.
pub cap record MemDir {
    state files: Map[Path, Text]
}

impl Dir for MemDir

impl MemDir {
    /// A `Dir` that holds `files`, each keyed by its path.
    pub fn with_files(files: Map[Text, Text]) -> Dir[read, list, write, create, delete]
}
```

`MemDir` is written in Proviso (§9.6). A path is a key, compared as written. A directory is any path that a file's path continues with `/`, and the root, `""`, is always one. Its failures read as the runtime's `Dir`'s do (OPEN_QUESTIONS P5).

## std.pool

```proviso
/// A collection whose elements are addressed by handles (§5.5). A pool is unique, so it moves and is never copied.
pub opaque unique record Pool[T]

/// A slot in one pool, and the generation of the element it was issued for.
pub opaque record Handle[T] derives(Eq, Hash)

impl[T] Pool[T] {
    /// An empty pool with a new identity.
    pub fn new() -> Pool[T]

    pub fn len(self) -> Int
        ensures result >= 0

    /// Stores `value` and returns a handle with a generation no other handle has had.
    pub fn insert(inout self, value: take T) -> Handle[T]

    /// Removes the element and returns it. Returns `None` if `handle` is stale or belongs to another pool.
    pub fn remove(inout self, handle: Handle[T]) -> Option[T]

    /// Replaces the element with `change(element)`. Returns `false`, and doesn't call `change`, if `handle` is stale or belongs to another pool.
    pub fn update(inout self, handle: Handle[T], change: fn(take T) -> T) -> Bool
}

impl[T: Copy] Pool[T] {
    /// The element, or `None` if `handle` is stale or belongs to another pool.
    pub fn get(self, handle: Handle[T]) -> Option[T]

    /// A new pool with the same elements and a new identity. Handles into `self` aren't valid in it.
    pub fn duplicate(self) -> Pool[T]
}
```

`pool[h]` borrows the element, as `xs[i]` does, so only copying it needs `T: Copy`. A stale or wrong-pool handle is a `stale_handle` defect.

## std.num

```proviso
/// Why a conversion failed.
pub enum ConversionError derives(Eq, Show) {
    OutOfRange
    NotANumber
}
```

## std.text

```proviso
/// Why `parse` failed.
pub enum ParseError derives(Eq, Show) {
    Empty
    Invalid
    OutOfRange
}
```
