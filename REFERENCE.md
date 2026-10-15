# Proviso — Working Reference

*v3 draft · phase 1 of the v1 implementation exists (README)*

This is the reference an agent keeps in context while writing Proviso. It aims to be complete enough to write correct code and short enough (~10K tokens) to stay loaded (P1). Normative detail beyond it is served by `proviso explain <rule>`. Choices that are experiment variables are tagged **(H*n*)**. Unresolved design questions are tagged **(Q*n*)**, tooling questions **(T*n*)** and process questions **(P*n*)**. All of them are listed in [OPEN_QUESTIONS.md](OPEN_QUESTIONS.md). The reasoning behind the design is in [RATIONALE.md](RATIONALE.md).

## 0. Principles

1. **Minimize the code and reasoning a correct change requires.** Do it with trustworthy boundaries, not by removing abstraction. An abstraction is welcome if its contract is as checkable as the code it hides.
2. **Every guarantee states how it is enforced** (§8.4). A plausible contract with weak enforcement is worse than none.
3. **Nothing hidden.** No ambient authority, no implicit conversions beyond subtyping (§9.2), no exceptions, no runtime contract checks you didn't ask for, and no dispatch targets the tools cannot list. Built-in safety checks (overflow, bounds, division by zero, stale handles) are inserted only where the verifier cannot rule the defect out from admissible facts (§8.4), and `proviso query defects` lists every one.
4. **Familiar syntax by default.** Departing from Rust/Swift/TypeScript/Python conventions needs experimental evidence.
5. **The compiler is a service.** It answers questions, applies structured edits and reports how contracts change (§15).

## 1. At a glance

```proviso
use std.fs { Dir, Path, FsError }                    // explicit names only, no globs
use std.io { IoError }

type UserId = distinct Int derives(Eq, Hash, Show)    // nominal; no implicit conversion

pub record User derives(Eq, Show) {
    id:   UserId
    name: Text where not name.is_empty()              // refinement: proven at every construction
    age:  Int  where 0 <= age and age < 150
}

pub enum LoadError derives(Show) {
    Io(cause: FsError)
    BadLine(line_no: Int)
}

pub fn main(sys: keep System) fails IoError {         // all authority starts here
    try sys.stdout.write_line("hello")
}

// Authority and failure are both in the signature.
pub fn load(dir: Dir[read], path: Path) -> List[User] fails LoadError {
    let text = dir.read_text(path) else fail LoadError.Io(cause: it)
    var users: List[User] = []
    for (i, line) in text.lines().enumerate() {
        users.push(try parse(line: line, line_no: i + 1))   // `try`: propagate, marked at the call
    }
    return users
}

fn parse(line: Text, line_no: Int) -> User fails LoadError {
    todo("split on commas, validate")                 // typed hole: needs --incomplete; reaching it is a defect
}

fn bump(counts: inout Map[Text, Int], key: Text) {    // inout: exclusive; committed only on success
    let n = counts.get(key) else 0
    counts.set(key: key, value: n + 1)
}

fn demo() {
    var counts: Map[Text, Int] = [:]
    bump(counts: &counts, key: "a")                   // `&` marks mutation at the call site
    let evens = [1, 2, 3, 4].filter(|x| x % 2 == 0)    // closures are non-escaping by default
    debug(counts, evens)                              // dev builds only
}

example bump_twice() == 2                             // examples sit next to code and run as cached tests
fn bump_twice() -> Int {
    var c: Map[Text, Int] = [:]
    bump(counts: &c, key: "k")
    bump(counts: &c, key: "k")
    return c.get("k") else 0
}
```

## 2. Lexical structure

- **Source and identifiers.** Source is UTF-8. Identifiers are ASCII `[A-Za-z_][A-Za-z0-9_]*`. Case is enforced: types, interfaces, enum variants, and type, effect and tag parameters are `PascalCase`; everything else is `snake_case`, including modules, functions, fields, units, tags and permissions.
- **Comments.** Comments are `// …`. Doc comments `/// …` attach to the next item and appear in `proviso sig`.
- **Statement ends.** A newline ends a statement; there are no semicolons (H8). A statement continues onto the next line in four cases:
  - the innermost unclosed bracket is `(` or `[`;
  - the line ends with a binary operator, `=` or `,`;
  - the next line begins with `.`, `else`, `and` or `or`;
  - the next line begins with a header clause (`fails`, `needs`, `requires`, `ensures`, `invariant`, `trusted`, `where`), or is a lone `{` opening the body of the header above it.
- **Expression statements.** An expression statement must be a call, an assignment or a control expression. A bare value is an error, except as the final expression of a closure or of an `if`, `match`, `scope` or `else` block, which is that block's value.
- **Function bodies** of non-`Unit` functions end every path with an explicit `return`; they have no implicit final-expression value.
- **Blocks** use braces (H1).
- **Literals:**

  | Kind | Examples |
  |---|---|
  | Integers | `42`, `1_000`, `0xff`, `0b1010` |
  | Floats | `1.5`, `2e-3` |
  | With a unit | `3.0[m]` |
  | Booleans | `true`, `false` |
  | Chars | `'a'` |
  | Text | `"…"` with escapes `\n \t \\ \" \u{1F600}` |
  | Interpolated text | `f"{name} is {age}"` (H7) |
  | Raw and multi-line text | `r"…"`, `"""…"""` |
  | Collections | list `[a, b]`, map `["k": v]`, empty map `[:]`, range `a..b` (half-open), inclusive range `a..=b` |

- **Literal types.** A literal is untyped until it meets an expected type: a declared type, a parameter, a return type, or the other operand of a binary operator. An integer literal can become any integer type that holds it, and a float literal any float type. With no expected type, integers are `Int`, floats `Float` and text `Text`. This is inference, not conversion: once chosen, a literal has exactly one type.
  - A literal never becomes a `distinct` type; write `UserId(7)`.
  - When a literal meets a refined type, the refinement is an ordinary obligation, discharged by the literal's value.
  - A unit is part of a literal (`3.0[m]`), and a bare literal has no unit (§4.7).
- **Keywords:** `all and any as assert attempt break cap check continue debug derives distinct effect effects else ensures enum example expect extern fail fails fn for if impl in inout interface invariant is it keep let loop match needs not observes opaque or pred property pub record requires resource return scope scoped self Self state tag take test todo trusted try type unique unit unreachable use uses var where while with`. Some words are contextual: `old` and `result` have meaning only inside `ensures`, and `pure` only after `trusted`. Keywords may still be used as method names after `.` (`s.with(…)`) and as module path segments (`std.test`).

## 3. Modules and names

- **Modules.** A file is a module: `src/net/http.proviso` is module `net.http`. A dependency's modules are prefixed with the package name, and the standard library is `std.*`. Top-level items are order-independent.
- **Imports.** `use a.b { X, y }` imports names. `use a.b` makes `b` usable as a qualifier, as in `b.y()`. `as` is allowed only to resolve a name collision (Q24). There are no glob imports (H12).
- **Visibility.** Items are private to their module by default. `pub` exports from the package and `pub(pkg)` exports within the package. A `pub record` exposes its fields and constructor; a `pub opaque record` exposes only the type and its `pub` methods. A `pub` item may not mention a private type in its signature, its contracts or, for a `pub record`, its fields.
- **Re-exports** for facades: `pub use internal.parser { parse_document }`. `proviso query def` always reports the original definition.
- **One name, one symbol.** Every reference resolves to exactly one symbol, and a module has at most one item per name, so there is no overloading. The same name in different modules is fine.
- **Methods.** Inherent methods live in `impl T { … }` in T's module. Interface methods live in `impl I for T` (§4.9). A method call `x.f()` must resolve to exactly one candidate, considering T's inherent methods and the methods of in-scope interfaces T implements. If it is ambiguous, call it as `I.f(x)`. Declaring an inherent method with the same name as a method of an interface T implements is an error.
- **No shadowing (H4).** A local, parameter or pattern binding may not reuse a name already in scope in the same function, including imported names.
- **No global mutable state.** Top-level `let` constants must be evaluable at compile time (Q19).
- **Prelude.** Without an import, a module sees exactly:
  - scalar types (§4.1), `Text`, `Bytes`, `Unit`, `Never`, `List`, `Map`, `Set`, `Array`, `Option`, `Result`, `Outcome`, `Defect`, `System`;
  - the enums `Ordering` and `Rounding`, and `Invalid` (the error of generated validators, §4.4);
  - the interfaces `Eq`, `Ord`, `Hash`, `Show`, `Copy`, `Index`, `Abandon`, `Add`, `Sub`, `Mul`, `Div`, `Neg`;
  - the variants `Some`, `None`, `Ok` and `Err`, the only variants that may be used unqualified in expressions.

### Calls and argument labels (H3)

Arguments are labelled with parameter names, in declaration order, with three exceptions:
- the receiver of a method call is not labelled;
- for a function, method or constructor with exactly one parameter besides the receiver, the label is optional;
- calls of function values take no labels, because closure parameters have none.

```proviso
counts.set(key: k, value: 1)    counts.get(k)    UserId(7)    User(id: i, name: n, age: a)
```

## 4. Types

### 4.1 Scalars
| Type | Meaning |
|---|---|
| `Int` | 64-bit signed integer; the same type as `Int64` |
| `Int8`, `Int16`, `Int32`, `Int64` | signed integers |
| `UInt8` … `UInt64`, `Byte` (= `UInt8`) | unsigned integers |
| `Float` | IEEE binary64 |
| `Float32` | IEEE binary32 |
| `Bool` | `true` / `false` |
| `Char` | a Unicode scalar value |
| `Unit` | the empty value `()`; an omitted return type means `Unit` |
| `Never` | the type of expressions that do not return |

Section 12 covers arithmetic and conversions.

### 4.2 Collections, Option, Result
- **Collections.** `List[T]`; `Map[K, V]` and `Set[T]`, which iterate in insertion order and require `K: Eq + Hash`; `Array[T, N]` of fixed length; tuples `(A, B)`.
- **`Option[T]`** is `Some(x)` or `None`.
- **`Result[T, E]`** is `Ok(x)` or `Err(e)`. It is mainly produced by `attempt` (§7.2).
- **Collection operations** (`map`, `filter`, `enumerate`, `lines` and so on) are eager and return new collections (Q12).

### 4.3 Text and Bytes
`Text` is immutable UTF-8 and is never indexed by integers (§12.3). `Bytes` is a separate type.

### 4.4 Records
```proviso
record Span derives(Eq) {
    lo: Int
    hi: Int
} where lo <= hi                                       // record-level refinement

let s = Span(lo: 1, hi: 4)                             // all fields, in order, labelled per §3
let t = s.with(hi: 9)                                  // functional update; refinements re-verified
```
- **Generics.** Records can be generic: `record Pair[A, B] { first: A, second: B }`.
- **Derives.** `derives(Eq, Ord, Hash, Show)` generates the implementations. `proviso query expand Span` shows the generated code (Q20).
- **Validation.** A record with refinements also gets `Span.validate(lo:, hi:) -> Span fails Invalid` (§8.4). An `Invalid` value names the failing field and predicate.
- **`with` and ownership.** `with` copies a record. On a record that holds a unique or resource value it consumes the original instead, as a `take self` method.

### 4.5 Enums
```proviso
enum Shape {
    Circle(radius: Float[m])
    Rect(w: Float[m], h: Float[m])
    Empty
}
let c = Shape.Circle(radius: 2.0[m])                   // variants are qualified in expressions
```
- **Patterns** may omit the enum name (§6.4).
- **Recursive enums** are allowed, and the compiler boxes them implicitly (Q26).

### 4.6 Aliases and distinct types
- **Aliases.** `type Name = Text` is a transparent alias.
- **Distinct types.** `type UserId = distinct Int derives(Eq, Hash, Show)` is a new nominal type. Construct with `UserId(7)` and unwrap with `id.value`. A distinct type inherits only what it lists in `derives`, so arithmetic must be opted into, for example `derives(Add, Sub)`.
- **Refinements on distinct types:** `type Percent = distinct Int where 0 <= self and self <= 100`.

### 4.7 Units and tags
- **Unit declarations** go at top level: `unit m`, `unit s`, `unit cm = 0.01 m`.
- **Quantities** use them: `Float[m]`, `Float[m/s]`, `Int[ms]`.
  - `*` and `/` combine units. `+`, `-` and the comparisons require equal units.
  - A bare literal has no unit, so `let d: Float[m] = 3.0` is an error. Write `3.0[m]`.
  - `d.to::[cm]()` converts between related units and `d.value_in::[m]()` strips the unit (Q23).
- **Tags** are phantom type arguments that keep values apart without runtime cost:
  ```proviso
  tag world
  tag local
  record Vec3[S: tag] { x: Float[m], y: Float[m], z: Float[m] }
  fn to_world(v: Vec3[local], frame: Frame[local, world]) -> Vec3[world] { … }
  ```

### 4.8 Generics
- **Syntax.** Type parameters go in `[]`, and constraints are explicit: `fn max[T: Ord + Copy](a: T, b: T) -> T`. Combine constraints with `+`: `T: Ord + Show`.
- **Type arguments** are inferred at calls, or given explicitly with `::[…]`: `max::[Int](a: 1, b: 2)` (H11). In an expression, `x[…]` is always indexing.
- **Compilation.** Generics are monomorphized.
- **Effect parameters** are written `effect E` (§9.5).
- **Copying and reach.** A type parameter is not assumed copyable, and it may have reach (§5.1). Copying a `T`, or storing or returning a borrowed `T`, requires `T: Copy`. Borrowing and moving need no constraint.

### 4.9 Interfaces
```proviso
pub interface Show {                     // as declared in the prelude
    fn show(self) -> Text
}

impl Show for Span {
    fn show(self) -> Text { return f"[{self.lo}, {self.hi})" }
}
```
- **Explicit implementations.** There is no structural conformance. An `impl` lives in the module of the interface or of the type.
- **Contracts on interface methods** bind every implementation. An implementation provides each `ensures` clause at the interface's level, or replaces `[tested]` or `[doc]` with `[checked]` or `[verified]`, or `[checked]` with `[verified]`. It takes the interface's `requires` clauses exactly as written, so its body assumes only what their levels allow. Callers through the interface rely only on the interface's levels (§8.4).
- **No default methods** (Q13).
- **Static dispatch.** A parameter of interface type, `x: Show`, means `[T: Show](x: T)`.
- **Dynamic dispatch** is explicit: `any Show`, for example `List[any Show]` (Q14). Because compilation is whole-program, `proviso query dispatch <call site>` lists every possible target. Capability interfaces are the exception: they are types in their own right and always dispatch dynamically (§9.2).
- **Operators.** `==` and `!=` come from `Eq`, ordering from `Ord`, arithmetic from `Add`, `Sub`, `Mul`, `Div` and `Neg`, and `x[i]` from `Index`. Scalars have these operators built in, including IEEE `==` and `<` on `Float` (§12.2). There are no custom operators.

## 5. Values, bindings and mutation

### 5.1 Values, ownership and reach
Every type has an ownership kind:

| Kind | Copies | Dropping | Examples |
|---|---|---|---|
| copyable (the default) | implicit | allowed | `Int`, `Text`, `List[User]`, capability handles |
| unique | none; the value moves or is borrowed | allowed | `Pool[T]`, `unique record` types |
| resource | none; the value moves or is borrowed | not allowed: consume it, or it is abandoned on failure (§10) | `File`, `Txn` |

- **Aggregates** take the strongest kind among their contents, in the order resource, unique, copyable. So `Option[File]`, `Result[File, E]` and `List[File]` are resources, and a record holding a `Pool` is unique.
- **Reach** is a separate axis. It is the set of capabilities a value can reach through its own permissions, its fields, its captures and its type arguments. Any value with reach follows the retention rules (§9.3), whatever its kind.
- **Value semantics** hold for everything except capability handles: assignment and passing never create sharing that code can observe, and there is no null. Copies of a capability handle share its underlying state (§9.6). Storage sharing behind other values is an implementation detail (see the implementation notes in OPEN_QUESTIONS.md).
- **`Copy`** is satisfied by copyable types with no reach. It cannot be implemented by hand (§4.8).
- **Moves.** Binding a unique or resource value to a new name, or passing it to a `take` parameter, moves it. The old name is unusable afterwards.
- **Bindings.** `let` is immutable and `var` is mutable.
- **Annotations.** Types are required on the parameters of named functions, on return types, fields and top-level constants. They are optional on locals and closure parameters.

### 5.2 Parameter modes
| Mode | Declared | Caller writes | Meaning |
|---|---|---|---|
| borrow (default) | `x: T` | `f(x: v)` | read-only for the duration of the call (except a capability's `state`, §9.6); a unique or resource value is lent, not consumed |
| inout | `x: inout T` | `f(x: &v)` (H5) | exclusive mutable access, committed on success (§5.4) |
| take | `x: take T` | `f(x: v)` | transfers ownership of a unique or resource value, which is unusable afterwards; for data it only avoids a copy |
| keep | `x: keep C` | `f(x: c)` | the callee may retain capability `c` (§9.3) |

Receivers are `self`, `inout self` or `take self`. Calling an `inout self` method requires a `var` or `inout` receiver, with no `&`.

### 5.3 Exclusivity
- **The rule.** While an `inout` access to a variable or one of its parts (field, element) is active, no other access to that variable is allowed.
- **Overlapping arguments.** `swap(a: &xs[i], b: &xs[j])` is rejected unless the parts are provably disjoint: different fields, or a fact `i != j` is in scope. Otherwise use `xs.swap(i: i, j: j)`.
- **Closures.** A closure that mutates a captured `var` holds exclusive access to it while the closure is live. For atomicity, that `var` counts as an `inout` argument of the call the closure is passed to (§5.4).

### 5.4 Failure atomicity
- **The rule.** If a call fails (an error exit), every `inout` argument is left exactly as it was before the call. Writes are committed only on success.
- **Resources are not rolled back.** Atomicity covers copyable and unique values. An `inout` argument that holds a resource is never rolled back, because resources can't be copied. It behaves as `inout(partial)`, and `sig` says so. Capability `state` follows its own rule (§9.6).
- **Implementation.** Copy-in/copy-out, with the copy elided when no failure point follows the first write.
- **Opting out.** `x: inout(partial) T` lets failures leave partial changes, and `proviso sig` reports it (Q8). Every value it leaves still satisfies its type's refinements, because every assignment must (§8.3). A part of a refined value, such as `&span.lo`, cannot be passed as `inout(partial)`.
- **Identity is never rolled back.** Restoring a pool on failure restores its contents, not its generation counters (§5.5).
- **Defects** (§7.3) and **cancellation** (§11) abort the whole task, so there is nothing left to commit.

### 5.5 Identity: pools and handles
There are no stored references. Identity is a handle into a pool:

```proviso
use std.pool { Pool, Handle }

var people: Pool[Person] = Pool.new()
let h: Handle[Person] = people.insert(p)
people.get(h)            // Option[Person]: None once removed, never another value
people.update(handle: h, change: |x| x.with(age: x.age + 1))
people.remove(h)
let q = people[h]        // through Index; a defect if h is stale
```

A handle records its pool's identity and a slot generation.
- **Pools are unique** (§5.1). `let b = a` moves a pool and never copies it. `a.duplicate()` makes a new pool with the same contents and a fresh identity; handles into `a` are not valid in the duplicate.
- **Generations are never reused.** Every insert takes a new generation, rollback (§5.4) does not restore generation counters, and a slot whose 64-bit generation would overflow is retired. So a handle that escapes from a failed call is stale afterwards.
- **Stale or wrong-pool handles** make `get` return `None`; `pool[h]` is a defect (Q18).

## 6. Expressions and control flow

### 6.1 Operators, from highest to lowest precedence
1. postfix: call, `.field`, `.method()`, `[index]`
2. prefix `-`; also `try` and `attempt`, which cover the whole postfix chain to their right (`try a.b().c()` covers both calls)
3. `*` `/` `%`
4. `+` `-`
5. `..` `..=`
6. `==` `!=` `<` `<=` `>` `>=` `in` `is`. These are non-associative, so `a < b < c` is an error.
7. `not`, which binds looser than comparison: `not a == b` means `not (a == b)` (H2)
8. `and`, `or`. Mixing them without parentheses is an error (H2).
9. `else` forms (§6.6), lowest: `m.get(k) else 0 + 1` means `m.get(k) else (0 + 1)`. In an `if` or `while` condition an `else` form must be parenthesized: `if (m.get(k) else false) { … }`. `fail e` takes everything to its right.

Other operator rules:
- **Bitwise operations** are named functions (`bit_and`, `bit_or`, `bit_xor`, `shl`, `shr`), so they have no precedence traps.
- **No casts.** There is no `as` cast; conversions are named functions (§12).
- **Assignment** is a statement, never an expression. `+=`, `-=`, `*=` and `/=` exist.

### 6.2 if
A condition must be `Bool`; there is no truthiness. `if` is an expression when it has an `else`.

### 6.3 match
```proviso
let label = match age {                 // facts make this exhaustive: 0 <= age < 150
    0..18 => "minor"
    18..150 => "adult"
}
match problem {
    Io(cause) => report(cause)
    BadLine(line_no) if line_no > 1 => skip()
    BadLine(_) => fail problem
}
```
- **Exhaustiveness** is checked. For integer ranges it uses refinement facts, which makes that check `[verified]` rather than `[type]`.
- **No fallthrough.**
- **Arms** are `pattern => expr` or `pattern => { … }`, with optional guards `if cond`.

### 6.4 Patterns
- **Forms:** literals, ranges, `_`, bindings, tuples `(a, b)`, variants (including `Some(x)`, `None`, `Ok(v)`, `Err(e)`), and records.
- **Variant fields.** For a variant with one field, a bare name binds that field whatever it is called: `Circle(r)`, `Some(x)`. With several fields, a bare name must match a field name, as in `Rect(w, h)`. `field: name` renames: `Rect(w: width, h: height)`.
- **Records:** `User(name, age: a, ..)` ignores the rest with `..`.
- **Ownership.** Matching a unique or resource value moves its contents into the bindings; matching a borrowed value borrows them.
- **Testing with `is`:** `if shape is Circle(radius) and radius > 1.0[m] { … }`. Bindings scope over the rest of the `and` chain and over the then-block.

### 6.5 Loops
- **`for pat in expr`** iterates lists, sets, maps (as `(k, v)`) and ranges.
- **Consuming loops.** `for x in take xs` consumes a collection element by element. It is how a collection of resources is used up (§10).
- **Other loops:** `while cond`, `loop`.
- **Control:** `break` and `continue`, with labels like `outer: for … { break outer }`.
- **Invariants:** a loop may carry `invariant P` clauses before its body (§8).

### 6.6 Unwrapping with else
These forms apply to an `Option[T]` or to a fallible call (§7):

| Form | Effect |
|---|---|
| `e else fail E.X(cause: it)` | fail the function; `it` is the error (not available for `Option`) |
| `e else value` | substitute a value of type `T` |
| `e else { … }` | the block either diverges (`return`, `fail`, `break`, `continue`) or ends in a `T` |
| `let (a, b) = e else …` | destructure the success value |

### 6.7 Closures
- **Syntax:** `|x| expr`, `|a: Int, b: Int| -> Int { … }`, `|| expr`.
- **Lifetimes.** The parameter a closure is passed to decides how long it may live and what it may capture:

  | Parameter | The closure may live | It captures |
  |---|---|---|
  | `f: fn(…)` (default) | until the call returns | locals by reference (mutation per §5.3) |
  | `f: scoped fn(…)` | until the enclosing `scope` ends (§11) | values by copy, with unique and resource values moved; borrowed capabilities; nothing mutably |
  | `f: keep fn(…)` | indefinitely | values by copy, with unique and resource values moved; `keep` capabilities only; nothing mutably |

  In every case, the closure's reach appears in its type, and the parameter must admit it with `uses` or `with E` (§9.4).

## 7. Errors and defects

### 7.1 Errors
- **One error type per function.** A function that can fail declares exactly one error type with `fails E` (Q1).
- **`fail e`** exits the function with error `e`.

### 7.2 Every fallible call is marked
| Marker | Meaning |
|---|---|
| `try f(…)` | propagate the error unchanged; the error types must be equal (H6) |
| `f(…) else fail E.X(cause: it)` | convert the error |
| `f(…) else v` or `else { … }` | handle the error |
| `attempt f(…)` | reify the outcome as `Result[T, E]` for `match` |
| `expect f(…) == v`, `example f(…) == v` | assert success with value `v`; a failure fails the test (§14) |
| `expect f(…) fails P`, `example f(…) fails P` | assert failure matching pattern `P` (§14) |

An unmarked fallible call is a compile error. The one exception is a call through an effect variable inside an effect-polymorphic function (§9.5).

### 7.3 Defects
Defects are bugs, not errors. They include:
- integer overflow, division by zero, an index out of bounds;
- a failed `assert`, `requires(checked)` or `ensures(checked)`;
- `unreachable`, reaching a `todo`, a stale or wrong-pool handle in `pool[h]`, a `TextPos` used with another text;
- stack exhaustion, out of memory.

What happens on a defect:
- The current task aborts, and its resources are abandoned (§10).
- The enclosing scope cancels its other tasks and propagates the defect as a defect (never as an error), and so on up to `main`.
- `main` exits with code 70 and writes a post-mortem: `proviso postmortem <id>` shows every frame's locals as JSON.
- Stack exhaustion and out-of-memory are process-fatal. Cleanup is not guaranteed, and the post-mortem is best effort (§10).
- Only `supervise` at a task boundary can catch a defect (§11).

`fails E` lists every recoverable failure. `proviso query defects f` lists the defect sites in `f` that the verifier could not rule out. Those are the only places the compiler inserts checks. Stack and memory exhaustion can happen anywhere and are not listed.

### 7.4 main
`pub fn main(sys: keep System) fails E` requires `E: Show`. On failure, the program prints `e.show()` to stderr and exits with code 1.

## 8. Contracts, refinements and verification

### 8.1 The predicate fragment
Predicates may use:
- Boolean operators, linear integer arithmetic and comparisons;
- `len()` and `is_empty()` of collections, and `byte_len()` and `is_empty()` of text;
- `in` with ranges, `is` variant tests, and field access;
- `old(x)` and `result` inside `ensures`;
- bounded quantifiers: `all i in a..b: P` and `any i in a..b: P`;
- standard predicate methods with verifier support: `xs.is_sorted()`, `xs.is_permutation_of(ys)`, `xs.is_unique()`, `xs.contains(x)`;
- user-defined `pred` functions whose bodies stay inside the fragment.

Anything else is `unsupported` (§8.5, Q9).

### 8.2 Where predicates appear
- field `where` clauses, record-level `where`, and `distinct … where self …`;
- `requires`, `ensures` and `invariant` clauses;
- `check` and `assert` statements.

```proviso
pub fn sort[T: Ord](values: inout List[T])
    ensures values.is_sorted()
    ensures values.is_permutation_of(old(values))
{
    …
}
```

### 8.3 Facts
The verifier reasons only from admissible facts (§8.4):
- the refinements of the types of values in scope;
- the current function's `requires`, at the levels its body may assume;
- the admissible `ensures` of functions it calls;
- the value each `let` binds, and the last value assigned to each `var`;
- loop facts: `a <= i < b` in `for i in a..b`, and `0 <= i < xs.len()` in `for (i, x) in xs.enumerate()`;
- branch conditions;
- successful `check` and `assert` statements.

Facts are dropped when the code changes what they describe:
- Assigning a `var`, or passing it with `&`, drops facts that mention it, except those the callee's admissible `ensures` re-establish.
- **Verification is modular.** A function's obligations are checked against the contracts of the functions it calls, never their bodies. Editing a body re-verifies only that body.

**Refinements under mutation.** A value must satisfy its type's refinements wherever it can be observed (Q28):
- **Every assignment** to a variable or to any part of it is an obligation that the whole value still satisfies its refinements, record-level ones included. With `span: Span`, `span.lo = 10` must prove `10 <= span.hi`.
- **Several fields at once:** assign a whole value, as in `span = span.with(lo: 10, hi: 20)`.
- **`inout` arguments** must match the parameter's type exactly, refinements included. Subtyping does not apply, because data flows both ways. Passing part of a refined value as `inout`, such as `&span.lo` or the `.value` of a refined `distinct` type, re-verifies every enclosing refinement when the call returns, using only the callee's admissible `ensures`. So does calling an `inout self` method on such a part.
- **Inside an `inout self` method**, the same rules apply to each assignment.
- **Capability `state`** (§9.6) can change behind any call that reaches the capability, so no fact about it survives such a call.

### 8.4 Enforcement levels
| Level | Written as | Meaning | May a proof assume it? |
|---|---|---|---|
| `[type]` | (implicit) | guaranteed by the type system: authority, retention, errors, exhaustiveness | yes |
| `[verified]` | `ensures P` (the default) | discharged statically within the budget | yes; its own trust dependencies carry over |
| `[checked]` | `ensures(checked) P`, `requires(checked) P`, `assert P` | checked at runtime; failure is a defect | yes, once the check has run |
| `[trusted]` | `ensures(trusted) P` on an `extern` | assumed, not checked (§13) | yes, recording a trust dependency (`proviso query trust`) |
| `[tested]` | `ensures(tested) P` | backed only by examples or property tests | **never** |
| `[doc]` | `ensures(doc) "text"` | a stated intent | **never** |

The levels are not one scale from weak to strong. `[tested]` and `[doc]` are evidence for readers and tests, never facts for the verifier, and bounds and overflow checks are removed only on the strength of admissible facts.

**`requires` at each level:**

| Clause | Who establishes it | May the body assume it? |
|---|---|---|
| `requires P` | every caller must prove it | yes |
| `requires(checked) P` | checked on entry; a failure is a defect reported at the call | yes, after entry |
| `requires(tested) P`, `requires(doc) "…"` | nobody | no; it only documents what callers should do |

**Contracts and refinements are checked at runtime only where you ask:** in `check` and `assert` statements and `(checked)` clauses. Refinements are always `[verified]`. To build a refined value from unvalidated data, use one of:
- `check P else fail E(…)`, which runs your check with your error and establishes P;
- `assert P`, which is a defect if false;
- the generated validator: `User.validate(…) fails Invalid`.

**There is no silent downgrade.** A `[verified]` clause that comes back unknown is a compile error. Changing it to `(checked)` or `(tested)` is an explicit edit, and `proviso diff-contracts` reports it as a weakening (Q10).

**Before a verifier exists**, the v1 implementation checks `[verified]` clauses and refinements at runtime instead, and labels them `[checked]` in `sig`. That way v1 never claims more than it enforces (P3).

### 8.5 Outcomes and budget
- **Four outcomes.** Each obligation ends as one of:
  - `proven`;
  - `refuted`, with counterexample values;
  - `unknown: unsupported`, meaning outside the fragment;
  - `unknown: budget`, meaning the resource limit was exceeded.
- **Budget units are deterministic, not wall-clock.** There is a default per obligation in `proviso.toml`.
- **Reproducibility.** Results are cached by obligation hash and must be reproducible on any machine with the same toolchain version (T8).

### 8.6 Fixes are alternatives
A diagnostic for an unproven obligation offers fixes labelled by behaviour:

| Fix | What it does |
|---|---|
| `validate` | add a `check`; you choose the error |
| `assert` | add an `assert` |
| `clamp` / `default` | change the data |
| `weaken` | edit the contract; lists the affected sites |
| `require` | push the obligation to callers |

A fix marked `changes_behavior: true` is never applied automatically (T7).

## 9. Capabilities and effects

### 9.1 No ambient authority
The standard library has no global file, network, clock, randomness, environment, process or console access. All authority comes from `main`, which receives the `System` record as `keep`, so it can hand capabilities to `keep` parameters:

```proviso
record System {                          // provided by the runtime
    fs: Dir[read, write, create, delete, list]
    net: Net[connect, listen]
    clock: Clock
    random: Random
    env: Env
    stdin: In
    stdout: Out
    stderr: Out
    process: Process[spawn]
}
```

### 9.2 Capability interfaces and permissions
```proviso
pub cap interface Dir observes(read, list) effects(write, create, delete) {
    fn read_text(self, path: Path) -> Text fails FsError                    needs read
    fn write_text(self, path: Path, text: Text) fails FsError               needs write
    fn size(self, path: Path) -> Int fails FsError                          needs read
    fn sub(self, path: Path) -> Self fails FsError     // same permissions, narrower root
}
```
- **Capability types.** A capability interface is a type in its own right. `Dir[read]` can be a parameter, field or return type, and calls on it dispatch dynamically to whichever implementation is behind it: the runtime's, or a fake (§9.6). Copies of a capability share its underlying state.
- **Two kinds of permission.** `observes` permissions cannot change anything outside the program, and `effects` permissions may. Inside an operation that needs only `observes` permissions, `self` is seen through an observes-only view: its `state` is read-only, and every capability it reaches is narrowed to its `observes` permissions. Helpers the operation calls receive that view.
- **Permission checks are static.** Calling an operation the static type does not permit is a compile error.
- **Reach.** A capability type also lists the other capabilities its implementation uses: `Dir[read] uses Out`. A bare `Dir[read]` uses none.
- **Subtyping.** `Dir[read, write]` is accepted where `Dir[read]` is expected, and `Dir[read]` where `Dir[read] uses Out` is expected. The language has four subtyping relations: permission sets; `uses` sets; refined types to their base type (`User.age` used as an `Int`); and `Never` to any type. There are no other implicit conversions (Q5).
- **Narrowing by type:** `dir.only::[read]()`.
- **Narrowing by value:** `dir.sub(path)` and `net.only_hosts(["api.example.com"])` (Q6).
- **Derived capabilities** (from `sub`, `only`, `only_hosts`) have the same retention as the capability they came from (§9.3).
- **What a signature guarantees.** A function can cause only the effects of the capabilities reachable from its parameters. Those are the capabilities passed directly, held in records, or captured by function-typed arguments, transitively (§9.4), and all of them are visible in the types. An opaque record declares its reach, as in `pub opaque record Cache uses Dir[read, write] { … }`, and the declaration is checked against its fields. A dynamic interface type does too: `any Show uses Out`, where a bare `any Show` admits only values with no reach. So `load_users(dir: Dir[read], …)` cannot write anything outside the program `[type]`, provided the runtime's own capabilities honour their permissions `[trusted]`.

### 9.3 Retention
- **Borrowed by default.** A parameter with reach, whether a capability or a value that holds or captures one, can be used and passed on during the call. It cannot be stored where it outlives the call, returned, or captured by a `keep` closure (§6.7). Anything derived from a borrowed capability is borrowed too.
- **`keep` allows retention.** A `keep` parameter may be retained, for example `fn open_cache(dir: keep Dir[read, write]) -> Cache`.
- **Records and containers with reach** follow the same retention rules, whatever their ownership kind (Q4).
- **Generics.** A type parameter may be instantiated with a type that has reach, and the instantiated type then has that reach. Generic code cannot call operations on a `T` without an interface constraint, and cannot store or return a borrowed `T` unless `T: Copy` (§4.8, Q31).

### 9.4 Function types and closures
- **Function types:** `fn(A) -> R`, optionally followed by `fails E`, `uses C` or `with E`. Here `C` lists capability types and `E` is an effect variable.
- **A closure's type** records the error it can fail with and its reach: the union of the reach of everything it captures, including other closures and values that hold capabilities. A closure that captures `dir` has a type like `fn(Path) -> Int uses Dir[read]`, and so does a closure that only captures that closure. A function type without `uses` admits only closures that capture no capabilities, so a parameter `f: fn() -> Text` cannot carry authority. What a closure may capture is also limited by its lifetime (§6.7).
- **Effect variables** range over both failure and `uses` (Q3).
- **Parameter modes** may appear in function types, as in `fn(inout Txn) -> T`.

### 9.5 Effect polymorphism
```proviso
impl[A] List[A] {
    pub fn map[B, effect E](self, f: fn(A) -> B with E) -> List[B] with E {
        var out: List[B] = []
        for x in self {
            out.push(f(x))          // calls through an effect variable are not marked
        }
        return out
    }
}

let users = try lines.map(|l| try parse(line: l, line_no: 0))   // E = fails LoadError: this call is fallible
let sizes = names.map(|n| dir.size(n) else 0)                   // E = uses Dir[read]: not fallible
```
- **Where marking happens.** Marking happens where `E` is concrete, at the outer call site.
- **No mixing.** A function with `with E` may not also declare its own `fails` (Q2).

### 9.6 Implementing capabilities and fakes
```proviso
cap record MemDir {
    state files: Map[Path, Text]       // shared by every copy of the capability
}

impl Dir for MemDir {
    fn read_text(self, path: Path) -> Text fails FsError {
        return self.files.get(path) else fail FsError.NotFound(path: path)
    }
    fn write_text(self, path: Path, text: Text) fails FsError {
        self.files.set(key: path, value: text)
    }
    …
}

let dir = Dir.of(MemDir(files: [:]))   // Dir[read, list, write, create, delete]
```
- **Capability handles share state.** Copies of a capability refer to the same underlying resource: the file system for the runtime's `Dir`, or the `state` fields of a Proviso implementation. This is the one exception to value semantics (§5.1).
- **`state` fields** are allowed only in a `cap record`, and a `cap record` value is a capability handle. Its `effects` operations may read, assign and mutate `state` through a plain `self`. Its `observes` operations may only read it (§9.2).
- **Atomic operations.** Calls on one capability object run one at a time. A Proviso-implemented operation runs with cancellation masked; a cancellation is delivered when it returns. Its `state` changes are committed only if it succeeds, so a failure or defect leaves `state` as it was. Calling back into the same object through a capability handle is a defect, while an implementation's direct calls to its own methods are ordinary calls (Q30).
- **An implementation's reach.** Its operations may use only the capabilities stored in its fields. `Dir.of(x)` has every permission and `uses` the capabilities in `x`. Operations for `observes` permissions may call only `observes` operations (§9.2).
- **Standard fakes.** `std.test` provides `MemDir`, `FakeClock`, `FakeNet` and `SeededRandom`, written in Proviso this way. Their constructors return capabilities directly.

### 9.7 debug
`debug(x, …)` writes debug representations, with the source location, to the debug stream. It needs no capability, and `proviso build --release` rejects it.

### 9.8 Replay
`proviso run --record` writes an ordered event log. It records every capability call, with its task, capability object, operation, arguments and result, in the global order in which calls complete. It also records when each call started, every channel, join and cancellation choice, and every cleanup-deadline expiry (§10, §11). Only calls on the runtime's capabilities are logged; Proviso-implemented capabilities are replayed by running their code. `proviso replay <run>` enforces the logged order and serves results from the log (T9).
- **Simulated by default.** Replay suppresses external effects and reproduces every result the program observed. A call whose arguments differ from the log is reported as a divergence, at the first point where the runs differ. Calls that overlapped on aliased resources, such as `dir` and `dir.sub("x")`, are reported, because their effect order may differ from their completion order.
- **`--live`** re-issues the effects one at a time, in logged order. It reproduces the run only if nothing outside the program changes those resources in the meantime.
- **Foreign code.** Calling an `extern` that is not `pure` makes the run non-replayable unless the extern is wrapped as a capability. A recording run reports when that happens (§13, T5).

## 10. Resources

```proviso
pub resource record Txn { conn: Conn }
impl Abandon for Txn {
    fn abandon(take self) { self.conn.rollback_quietly() }  // cannot fail
}
```
Every resource type implements `Abandon`. A `resource record` declares a base resource type, and any aggregate that contains a resource is a resource too (§5.1). I/O resources such as `File[read, write]` are also capabilities: they have permissions and reach (§9.2).

1. **One owner.** Passing a resource to a borrow parameter (the default) or an `inout` parameter lends it. Passing it to a `take` parameter transfers ownership. A `take self` method such as `commit` or `close` consumes it. Resources are never copied.
2. **On a normal exit**, every resource the scope still owns must have been consumed or transferred, or it is a compile error.
3. **On a failure exit**, whether `fail`, a `try` that propagates, a defect, or cancellation, the resources the scope still owns are abandoned in reverse order of acquisition.
4. **Aggregates.** Matching a resource-bearing value moves the contained resource into the binding (§6.4). Abandoning an aggregate abandons the active variant's resource, or each element in reverse order. `for f in take files { … }` consumes a collection element by element.
5. **No silent loss.** A resource cannot be overwritten or discarded. Assigning to a place that holds one, or dropping one that an expression produced, is a compile error. A container operation that would discard one returns it instead: `files.replace(…)` returns the old file. Error types cannot be resources.
6. **Lent resources cannot be consumed.** A borrowed or `inout` resource cannot be passed to `take` or used by a `take self` method. So a callback lent `tx` cannot commit it.

**Cleanup is bounded, not absolute** (Q29):
- **Deadline.** `abandon` runs with cancellation masked, under a cleanup deadline (default 10 s, set in `proviso.toml`). At the deadline, the runtime interrupts its pending capability call. If it still does not finish, as in a pure loop, the process aborts with exit code 70 and a post-mortem.
- **Defects during cleanup.** If `abandon` hits a defect, the defect is recorded and that resource is reported as leaked. The remaining resources are still abandoned, and the exit becomes a defect exit even if it began as an error (§7.3).
- **Fatal conditions.** Stack exhaustion and out-of-memory are process-fatal. Cleanup is not guaranteed, and the post-mortem is best effort.

Scoped helpers are ordinary functions with non-escaping closures:

```proviso
pub fn rename_user(db: Db[write], id: UserId, name: Text) fails DbError
    requires not name.is_empty()       // callers must establish this; it discharges User.name
{
    try db.transaction(|tx| {          // commits on normal exit, rolls back on failure
        let user = try tx.get(id)
        try tx.put(id: id, user: user.with(name: name))
    })                                 // tx is lent to the closure (inout Txn); transaction owns and commits it
}
```

## 11. Concurrency

```proviso
let pages = try scope |s| {
    let a = s.spawn(|| try fetch(net: net, url: u1))
    let b = s.spawn(|| try fetch(net: net, url: u2))
    [try a.join(), try b.join()]
}
```
1. **No shared mutable memory**, except capability `state`, which tasks reach only through atomic operations (§9.6). A `scope` waits for all its tasks; no task outlives its scope.
2. **Captures.** `spawn` takes a `scoped` closure (§6.7). It captures values by copy, with unique and resource values moved, and capabilities as borrows, which is safe because the scope outlives its tasks. It cannot capture a `var` mutably.
3. **Communication** goes through `Channel[T]`, which is bounded and carries values (Q15).
4. **Failure.** The first task to fail or hit a defect cancels its siblings. The scope waits for them, then fails with that first error, or propagates that first defect as a defect. The others are recorded in the trace.
5. **Cancellation** is cooperative, and it is not an error: `else`, `attempt` and `supervise` cannot catch it. It is delivered at capability calls, channel operations, `join`, `checkpoint()` and every loop back-edge, so even a pure loop can be cancelled. A cancelled task exits through the failure path, so its resources are abandoned.
6. **Determinism.** Data races on memory are impossible, because tasks share mutable memory only through atomic capability operations. Races through external resources are still possible: two tasks writing the same file through copies of a `Dir` can complete in either order. The completion order of capability calls is recorded with the other scheduling choices (§9.8), and `proviso test --schedules N` explores seeded orderings.
7. **Supervision.** `supervise(|| work())` runs `work` in a child task and returns an `Outcome[T, E]`: `Done(t)`, `Failed(e)` or `Crashed(d)`, where `d: Defect`. It is the only way to catch a defect (Q16).

`supervise`, `checkpoint` and `parallel_map` come from `std.task`.

## 12. Numbers and text

### 12.1 Integers
- **Overflow is a defect.** Named operations give other behaviour: `wrapping_add`, `saturating_add`, `checked_add` (which returns an `Option`), and so on.
- **Division.** `/` truncates toward zero, and `%` takes the sign of the dividend. `div_floor` and `mod_floor` are named functions. Dividing by zero is a defect.
- **Conversions are named:**
  - lossless: `Int64(x32)`;
  - fallible: `Int32.try_from(x) else …`;
  - wrapping: `Int32.wrapping_from(x)`;
  - parsing: `Int.parse(text) fails ParseError`.

### 12.2 Floats
- **Arithmetic** is IEEE-754 with round-to-nearest-even only. There is no rounding-mode control, no fast-math, and no implicit fused multiply-add (`x.mul_add(factor: y, addend: z)` is explicit). `+`, `-`, `*`, `/`, `sqrt` and conversions give bit-identical results on every platform.
- **NaN.** NaN bit patterns are not observable: `to_bits` returns one canonical NaN.
- **Library functions** such as `sin` and `exp` are reproducible only if the standard library implements them itself instead of calling the platform's maths library (Q27).
- **Comparison.** `==` follows IEEE. `Float` does not implement `Eq`, `Ord` or `Hash`; use `total_cmp` for sorting (Q22).
- **Conversions:** `Float.from(i)` rounds to nearest-even. `f.to_int(rounding: Rounding.TowardZero)` fails on NaN or on an out-of-range value.

### 12.3 Text
- **Encoding.** Text is UTF-8 and immutable. It has no `len()` and no integer indexing.
- **Measuring and iterating:** `byte_len()`, `chars()` for Unicode scalar values, and `graphemes(t)` from `std.text.unicode`.
- **Positions.** Searches (`find`, `find_last`) return `TextPos` values. A position is valid only for the text it came from; using it with another text is a defect (Q11). Slice with `t.slice(from: p, to: q)`.
- **Prefer operations that avoid positions:** `split_once(sep)`, `split(sep)`, `lines()`, `trim()`, `strip_prefix(p) -> Option[Text]`, `starts_with(p)`.
- **Comparison** is by code point, with no implicit normalization; `normalize_nfc()` is explicit.
- **Bytes:** `Text.from_utf8(bytes) fails Utf8Error`.

## 13. Foreign code

```proviso
extern "C" fn crc32(crc: UInt32, data: Bytes) -> UInt32
    trusted pure                                   // no I/O, deterministic, retains nothing

extern "C" fn sqlite_exec(db: Db[write], sql: Text) -> Int32
    trusted uses db                                // I/O must take its capability
```
- **Types that cross:** scalars, records made only of scalars, borrowed `Bytes` and `Text` (as pointer plus length), `inout` of those flat types (as pointers), and capabilities (as opaque handles).
- **Trust clauses.** Each `extern` declares `trusted pure` or `trusted uses <capability parameter>`, and optionally `ensures(trusted) P`.
- **Obligations on the C side**, which Proviso cannot check:
  - retain no borrowed argument after the call;
  - write only through `inout` parameters;
  - be safe to call concurrently;
  - be deterministic if declared `pure`.
- **Inspecting trust.** `proviso query trust f` lists every trusted clause `f` depends on, directly or transitively, and `proviso diff-contracts` reports new ones (Q21).

## 14. Tests, examples and properties

- **`example f(…) == v` or `example f(…) fails P`** is a top-level declaration placed next to the function.
  - An example cannot need capabilities.
  - It runs under `proviso test` and `proviso check --examples` with a fuel limit.
  - It is cached by the hash of the function and its transitive dependencies.
  - It appears in `proviso sig`.
- **`test "name" { … }`** blocks use `expect cond`, `expect f(…) == v` and `expect f(…) fails P`, where `P` is a pattern.
  - When an `expect a == b` fails, both values are reported.
  - Tests may build fakes (§9.6).
  - A test in the same module can see private items. Tests can also live under `tests/`.
- **`property "name" for (xs: List[Int], k: Int) { expect … }`** generates its inputs from the types, respecting refinements.
  - Failing inputs are shrunk and the seed is printed.
  - The failure is saved as a regression example.
- **`proviso test --affected-by <symbol>`** runs only the tests that can reach the symbol, using the static call graph plus dispatch sets.

## 15. Toolchain

### 15.1 Contract with agents
Whether these tools pay off is the central experiment (H10).

- **Two interfaces.** Every command accepts `--json`, and the same operations are available through `proviso serve` as JSON-RPC over stdio, also exposed as MCP tools (T4).
- **Stable codes.** Diagnostic codes are stable; they are catalogued in [tests/DIAGNOSTICS.md](tests/DIAGNOSTICS.md).
- **No cascades.** All errors are reported at once, and an error poisons only its dependents.
- **Broken code.** Queries and edits work on code that does not compile. An answer that depends on broken parts carries `"partial": true` (T1).
- **Locations.** Each location is given two ways: `file:line:col`, and a symbol anchor such as `users.parse_user+8` (line 8 of the item). The anchor stays stable when other items are edited (T3).
- **Revisions.** Every top-level item has a revision hash, which structured edits use (T2).
- **Canonical output.** The output of `sig`, `fmt` and `diff-contracts` is canonical and deterministic, so it can be checked in as golden files.

### 15.2 Commands
| Command | Purpose |
|---|---|
| `proviso check [--incomplete] [--examples]` | type-check and verify; `--incomplete` accepts `todo` (Q25) |
| `proviso build [--release]` | whole-program build through C; never accepts `todo`; `--release` also rejects `debug` |
| `proviso run [--incomplete] [--record]` · `proviso replay <run>` | run, where reaching a `todo` is a defect; deterministic replay |
| `proviso test [--incomplete] [--affected-by S] [--schedules N]` | examples, tests, properties |
| `proviso sig <module or symbol>` | contracts with enforcement levels, revisions, examples |
| `proviso query <kind> <target>` | `def refs callers callees impls dispatch type effects obligations defects trust costs expand` |
| `proviso explain <code or rule>` | normative text for a diagnostic or rule |
| `proviso edit <op> <symbol> --rev R` | `replace-body replace-item insert-item delete-item rename`; batches are atomic |
| `proviso diff-contracts A..B` | contract changes between two revisions |
| `proviso trace <symbol> -- <run args>` | log a function's calls and results without editing code; works on replays |
| `proviso postmortem <id>` | frames and locals of a defect |
| `proviso fmt [--check]` | canonical format; `--check` fails if a file would change |

### 15.3 Diagnostics
```json
{"code": "E0412", "kind": "refinement_refuted", "at": "src/users.proviso:34:12",
 "anchor": "users.parse_user+8", "message": "User.age requires 0 <= age and age < 150",
 "counterexample": {"age_text": " 900", "age": 900},
 "fixes": [
   {"kind": "validate", "changes_behavior": true, "needs": "error to fail with",
    "text": "check 0 <= age and age < 150 else fail <error>"},
   {"kind": "assert", "changes_behavior": true, "text": "assert 0 <= age and age < 150"},
   {"kind": "weaken", "changes_behavior": true, "target": "users.User.age", "affected_sites": 3}]}
```

### 15.4 Structured edits
```
$ proviso edit replace-body users.parse_user --rev 44b0c7 --from body.proviso --json
{"applied": true, "rev": "9d01aa", "contract_delta": [], "diagnostics": []}
{"applied": false, "reason": "stale_rev", "current_rev": "51c3e0", "current_text": "…"}
```
- **Output.** Every applied edit returns its contract delta and new diagnostics (H9).
- **Formatting.** Edited code is always in canonical format.

### 15.5 Contract diffs
```
$ proviso diff-contracts main..HEAD
users.load_users                                      BREAKING
  ~ authority   dir: Dir[read] → Dir[read, write]     widened: may now write files
  ~ fails       LoadError → LoadOrCacheError           callers' `try` no longer type-checks
  ~ on failure  no external writes → may leave partial writes
users.sort_by_age                                     WEAKENED
  ~ ensures     result.is_permutation_of(users): [verified] → [tested]
```
Each change is classified as `BREAKING`, `WEAKENED`, `STRENGTHENED`, `AUTHORITY` or `TRUST` (T6). The "on failure" line reports external writes (Q7).

## 16. Packages and formatting

- **Package files.** `proviso.toml` declares the package name, `lang = "0.3"` and the dependencies. `proviso.lock` pins dependencies by content hash.
- **Standard library.** It ships with the toolchain, and `proviso sig std.text` describes the installed version, not a remembered one.
- **Standard library quality.** Every public `std` function has a doc comment and its authority in its signature. It also has at least one contract, or `ensures(doc) "none"` stating that none applies.
- **Compilation** is whole-program; Proviso code is never linked dynamically.
- **Formatting.** There is one canonical format, applied by `proviso fmt`. `proviso check` reports a non-canonical file as a warning, never an error.

## 17. Worked example

```proviso
// src/users.proviso
use std.fs { Dir, Path, FsError }
use std.test { MemDir }

pub record User derives(Eq, Show) {
    name: Text where not name.is_empty()
    age:  Int  where 0 <= age and age < 150
}

pub enum LoadError derives(Eq, Show) {
    Io(cause: FsError)
    MissingComma(line_no: Int)
    EmptyName(line_no: Int)
    BadAgeText(line_no: Int, text: Text)
    AgeOutOfRange(line_no: Int, value: Int)
}

/// Reads `name,age` lines from `path` under `dir`.
pub fn load_users(dir: Dir[read], path: Path) -> List[User] fails LoadError {
    let text = dir.read_text(path) else fail LoadError.Io(cause: it)
    var users: List[User] = []
    for (i, line) in text.lines().enumerate() {
        users.push(try parse_user(line: line, line_no: i + 1))
    }
    return users
}

pub fn parse_user(line: Text, line_no: Int) -> User fails LoadError {
    let (name_text, age_text) = line.split_once(",")
        else fail LoadError.MissingComma(line_no: line_no)
    let name = name_text.trim()
    check not name.is_empty() else fail LoadError.EmptyName(line_no: line_no)
    let age = Int.parse(age_text.trim())
        else fail LoadError.BadAgeText(line_no: line_no, text: age_text)
    check 0 <= age and age < 150
        else fail LoadError.AgeOutOfRange(line_no: line_no, value: age)
    return User(name: name, age: age)     // the two checks discharge User's refinements
}

example parse_user(line: "ada, 36", line_no: 1) == User(name: "ada", age: 36)
example parse_user(line: "ada", line_no: 7) fails LoadError.MissingComma(line_no: 7)

test "a bad line reports its line number" {
    let dir = MemDir.with_files(["u.csv": "ada, 36\nbob\n"])
    expect load_users(dir: dir, path: Path("u.csv")) fails LoadError.MissingComma(line_no: 2)
}
```

```
$ proviso sig users
pub record User derives(Eq, Show)                                        rev 1a09f3
    name: Text where not name.is_empty()
    age:  Int  where 0 <= age and age < 150
    refinements   proven at all 2 construction sites                     [verified]

pub fn load_users(dir: Dir[read], path: Path) -> List[User] fails LoadError      rev 9e2210
    /// Reads `name,age` lines from `path` under `dir`.
    authority     dir: Dir[read], observes only, uses nothing, not kept  [type]
    on failure    no inout parameters; no writes outside the program     [type]
    trusts        the runtime's Dir honours its permissions              [trusted]
    defects       none unproven                                          [verified]

pub fn parse_user(line: Text, line_no: Int) -> User fails LoadError              rev 44b0c7
    authority     none                                                   [type]
    examples      2 passing, cached                                      [tested]
    defects       none unproven                                          [verified]
```
