# Proviso standard library through phase 2

This file lists the standard library items that phases 1 and 2 implement (OPEN_QUESTIONS Q36, P3). Each item is written as its declaration without a body. From phase 4, `proviso sig std` serves the same information from the installed toolchain (REFERENCE §16), and this file goes away.

- **Phase 1** already has `System.stdout`, `Out.write_line` and `IoError`. Everything else here is phase 2.
- **Contracts.** An `ensures` clause is listed where the verifier will need it (phase 5). The other items get theirs when `sig` exists (phase 4, T11). The toolchain implements these items natively and trusts them to meet their contracts, so the v1 profile doesn't check std contracts at runtime.
- **Later phases.** `map`, `filter` and the other operations that take a closure that may fail need effect variables (§9.5), which arrive in phase 3. Files, `Dir` and `In`'s operations also arrive in phase 3 (Q6).

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

pub enum Ordering {
    Less
    Equal
    Greater
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

`Hash` has no method that phase 2 code calls. It is only derived. `Copy` is satisfied automatically by copyable types with no reach (§5.1). `Index` is the built-in `xs[i]` and `pool[h]` below.

### Derived implementations

`derives(Eq, Ord, Hash, Show)` on a record or enum generates these implementations:

| Interface | Behaviour |
|---|---|
| `Eq` | Equal when the variants are equal and every field is equal. |
| `Ord` | Compares variants in declaration order, then fields in declaration order. |
| `Hash` | Consistent with the derived `Eq`. |
| `Show` | Writes the expression that builds the value: `User(name: "ada", age: 36)`, `LoadError.MissingComma(line_no: 7)`, `Stop.Halt`. Text and chars inside are quoted and escaped the way `debug` writes them (OPEN_QUESTIONS P5). |

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

`xs[i]` reads element `i` and needs `T: Copy`. An index out of bounds is an `index_out_of_bounds` defect. `xs[i] = v` replaces element `i`, under the same bounds check. If `T` is a resource, `xs[i] = v` is a compile error, because it would discard the old element (§10 rule 5).

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

## std.io

```proviso
/// A text output stream, such as `System.stdout`.
pub cap interface Out {
    /// Writes `text` followed by a newline.
    fn write_line(self, text: Text) fails IoError
}

/// A text input stream, such as `System.stdin`. Its operations arrive with `stdin` in phase 3.
pub cap interface In {}

/// An I/O failure. `show` gives the operating system's message.
pub opaque record IoError derives(Show)
```

`Out` has no permission list yet (Q6).

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

`pool[h]` reads the element and needs `T: Copy`. A stale or wrong-pool handle is a `stale_handle` defect.

## std.text

```proviso
/// Why `parse` failed.
pub enum ParseError derives(Eq, Show) {
    Empty
    Invalid
    OutOfRange
}
```
