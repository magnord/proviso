# Proviso — Working Reference

*v2 draft · design only, nothing implemented*

This is the reference an agent keeps in context while writing Proviso. It aims to be complete enough to write correct code and short enough (~10K tokens) to stay loaded (P1). Normative detail beyond it is served by `proviso explain <rule>`. Choices that are experiment variables are tagged **(H*n*)**. Unresolved design questions are tagged **(Q*n*)**, tooling questions **(T*n*)** and process questions **(P*n*)**. All of them are listed in [OPEN_QUESTIONS.md](OPEN_QUESTIONS.md). The reasoning behind the design is in [RATIONALE.md](RATIONALE.md).

## 0. Principles

1. **Minimize the code and reasoning a correct change requires.** Do it with trustworthy boundaries, not by removing abstraction. An abstraction is welcome if its contract is as checkable as the code it hides.
2. **Every guarantee states how it is enforced** (§8.4). A plausible contract with weak enforcement is worse than none.
3. **Nothing hidden.** No ambient authority, no implicit conversions beyond subtyping (§9.2), no exceptions, no compiler-inserted contract checks, and no dispatch targets the tools cannot list. Built-in safety checks (overflow, bounds, division by zero, stale handles) are inserted only where the verifier cannot rule the defect out, and `proviso query defects` lists every one.
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
- **Statement ends.** A newline ends a statement; there are no semicolons (H8). A statement continues onto the next line in three cases:
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

- **Keywords:** `all and any as assert attempt break cap check continue debug derives distinct effect else ensures enum example expect extern fail fails fn for if impl in inout interface invariant is it keep let loop match needs not opaque or perms pred property pub record requires resource return scope scoped self Self tag take test todo trusted try type unit unreachable use var where while with`. Some words are contextual: `old` and `result` have meaning only inside `ensures`, and `pure` and `uses` only after `trusted`. Keywords may still be used as method names after `.` (`s.with(…)`) and as module path segments (`std.test`).

## 3. Modules and names

- **Modules.** A file is a module: `src/net/http.proviso` is module `net.http`. A dependency's modules are prefixed with the package name, and the standard library is `std.*`. Top-level items are order-independent.
- **Imports.** `use a.b { X, y }` imports names. `use a.b` makes `b` usable as a qualifier, as in `b.y()`. `as` is allowed only to resolve a name collision (Q24). There are no glob imports.
- **Visibility.** Items are private to their module by default. `pub` exports from the package and `pub(pkg)` exports within the package. A `pub record` exposes its fields and constructor; a `pub opaque record` exposes only the type and its `pub` methods.
- **Re-exports** for facades: `pub use internal.parser { parse_document }`. `proviso query def` always reports the original definition.
- **One name, one symbol.** Every reference resolves to exactly one symbol, and a module has at most one item per name, so there is no overloading. The same name in different modules is fine.
- **Methods.** Inherent methods live in `impl T { … }` in T's module. Interface methods live in `impl I for T` (§4.9). A method call `x.f()` must resolve to exactly one candidate, considering T's inherent methods and the methods of in-scope interfaces T implements. If it is ambiguous, call it as `I.f(x)`. Declaring an inherent method with the same name as a method of an interface T implements is an error.
- **No shadowing (H4).** A local, parameter or pattern binding may not reuse a name already in scope in the same function, including imported names.
- **No global mutable state.** Top-level `let` constants must be evaluable at compile time (Q19).
- **Prelude.** Without an import, a module sees exactly:
  - scalar types (§4.1), `Text`, `Bytes`, `Unit`, `Never`, `List`, `Map`, `Set`, `Array`, `Option`, `Result`, `Outcome`, `Defect`, `System`;
  - the enums `Ordering` and `Rounding`, and `Invalid` (the error of generated validators, §4.4);
  - the interfaces `Eq`, `Ord`, `Hash`, `Show`, `Index`, `Abandon`, `Add`, `Sub`, `Mul`, `Div`, `Neg`;
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
- **Syntax.** Type parameters go in `[]`, and constraints are explicit: `fn max[T: Ord](a: T, b: T) -> T`. Combine constraints with `+`: `T: Ord + Show`.
- **Type arguments** are inferred at calls, or given explicitly with `::[…]`: `max::[Int](a: 1, b: 2)` (H11). In an expression, `x[…]` is always indexing.
- **Compilation.** Generics are monomorphized.
- **Effect parameters** are written `effect E` (§9.5).

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
- **Contracts on interface methods** bind every implementation. Each implementation must meet each contract at the interface's enforcement level or a stronger one.
- **No default methods** (Q13).
- **Static dispatch.** A parameter of interface type, `x: Show`, means `[T: Show](x: T)`.
- **Dynamic dispatch** is explicit: `any Show`, for example `List[any Show]` (Q14). Because compilation is whole-program, `proviso query dispatch <call site>` lists every possible target. Capability interfaces are the exception: they are types in their own right and always dispatch dynamically (§9.2).
- **Operators.** `==` and `!=` come from `Eq`, ordering from `Ord`, arithmetic from `Add`, `Sub`, `Mul`, `Div` and `Neg`, and `x[i]` from `Index`. Scalars have these operators built in, including IEEE `==` and `<` on `Float` (§12.2). There are no custom operators.

## 5. Values, bindings and mutation

### 5.1 Values
- **Value semantics everywhere.** Every type is a value type, so assignment and passing never create sharing that code can observe. There are no reference types and no null. Storage sharing is an implementation detail (see the implementation notes in OPEN_QUESTIONS.md).
- **Bindings.** `let` is immutable and `var` is mutable.
- **Annotations.** Types are required on the parameters of named functions, on return types, fields and top-level constants. They are optional on locals and closure parameters.

### 5.2 Parameter modes
| Mode | Declared | Caller writes | Meaning |
|---|---|---|---|
| borrow (default) | `x: T` | `f(x: v)` | read-only for the duration of the call |
| inout | `x: inout T` | `f(x: &v)` (H5) | exclusive mutable access, committed on success (§5.4) |
| take | `x: take T` | `f(x: v)` | consumes `v`, which is unusable afterwards; required for resources (§10) |
| keep | `x: keep C` | `f(x: c)` | the callee may retain capability `c` (§9.3) |

Receivers are `self`, `inout self` or `take self`. Calling an `inout self` method requires a `var` or `inout` receiver, with no `&`.

### 5.3 Exclusivity
- **The rule.** While an `inout` access to a variable or one of its parts (field, element) is active, no other access to that variable is allowed.
- **Overlapping arguments.** `swap(a: &xs[i], b: &xs[j])` is rejected unless the parts are provably disjoint: different fields, or a fact `i != j` is in scope. Otherwise use `xs.swap(i: i, j: j)`.
- **Closures.** A closure that mutates a captured `var` holds exclusive access to it while the closure is live. For atomicity, that `var` counts as an `inout` argument of the call the closure is passed to (§5.4).

### 5.4 Failure atomicity
- **The rule.** If a call fails (an error exit), every `inout` argument is left exactly as it was before the call. Writes are committed only on success.
- **Implementation.** Copy-in/copy-out, with the copy elided when no failure point follows the first write.
- **Opting out.** `x: inout(partial) T` lets failures leave partial changes, and `proviso sig` reports it (Q8).
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

A handle records its pool and a generation. Using it with the wrong pool is a defect (Q18).

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
- **Testing with `is`:** `if shape is Circle(radius) and radius > 1.0[m] { … }`. Bindings scope over the rest of the `and` chain and over the then-block.

### 6.5 Loops
- **`for pat in expr`** iterates lists, sets, maps (as `(k, v)`) and ranges.
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
  | `f: fn(…)` (default) | until the call returns | locals by reference (mutation per §5.3) and any capabilities |
  | `f: scoped fn(…)` | until the enclosing `scope` ends (§11) | values by copy and borrowed capabilities; nothing mutably |
  | `f: keep fn(…)` | indefinitely | values by copy and `keep` capabilities only; nothing mutably |

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
The verifier reasons from the facts in scope:
- the refinements of the types of values in scope;
- the current function's `requires`;
- the `ensures` of functions it calls;
- branch conditions;
- successful `check` and `assert` statements.

Facts are dropped when the code changes what they describe:
- Assigning a `var`, or passing it with `&`, drops facts that mention it, except those the callee's `ensures` re-establish.
- **Verification is modular.** A function's obligations are checked against the contracts of the functions it calls, never their bodies. Editing a body re-verifies only that body.

### 8.4 Enforcement levels
| Level | Written as | Meaning |
|---|---|---|
| `[type]` | (implicit) | guaranteed by the type system: authority, retention, errors, exhaustiveness |
| `[verified]` | `ensures P` (the default) | discharged statically within the budget |
| `[checked]` | `ensures(checked) P`, `assert P` | runtime check; failure is a defect |
| `[tested]` | `ensures(tested) P` | backed only by examples or property tests |
| `[doc]` | `ensures(doc) "text"` | a stated intent |
| `[trusted]` | `ensures(trusted) P` on an `extern` | assumed, not checked (§13) |

`requires` takes the same levels.

**Refinements are always `[verified]`.** The compiler never inserts a check for a contract or refinement. To build a refined value from unvalidated data, use one of:
- `check P else fail E(…)`, which runs your check with your error and establishes P;
- `assert P`, which is a defect if false;
- the generated validator: `User.validate(…) fails Invalid`.

**There is no silent downgrade.** A `[verified]` clause that comes back unknown is a compile error. Changing it to `(checked)` or `(tested)` is an explicit edit, and `proviso diff-contracts` reports it as a weakening (Q10).

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
pub cap interface Dir perms(read, write, create, delete, list) {
    fn read_text(self, path: Path) -> Text fails FsError                    needs read
    fn write_text(self, path: Path, text: Text) fails FsError               needs write
    fn size(self, path: Path) -> Int fails FsError                          needs read
    fn sub(self, path: Path) -> Self fails FsError     // same permissions, narrower root
}
```
- **Capability types.** A capability interface is a type in its own right. `Dir[read]` can be a parameter, field or return type, and calls on it dispatch dynamically to whichever implementation is behind it: the runtime's, or a fake (§9.6).
- **Permission checks are static.** Calling an operation the static type does not permit is a compile error.
- **Subtyping.** `Dir[read, write]` is accepted where `Dir[read]` is expected. The language has three subtyping relations: permission sets; refined types to their base type (`User.age` used as an `Int`); and `Never` to any type. There are no other implicit conversions (Q5).
- **Narrowing by type:** `dir.only::[read]()`.
- **Narrowing by value:** `dir.sub(path)` and `net.only_hosts(["api.example.com"])` (Q6).
- **Derived capabilities** (from `sub`, `only`, `only_hosts`) have the same retention as the capability they came from (§9.3).

### 9.3 Retention
- **Borrowed by default.** A capability parameter can be used, and passed on, during the call. It cannot be stored in a record, returned, or captured by a `keep` closure (§6.7). A capability derived from a borrowed one is borrowed too.
- **`keep` allows retention.** A `keep` parameter may be retained, for example `fn open_cache(dir: keep Dir[read, write]) -> Cache`.
- **Capability-bearing records.** A record with a field of capability type follows the same rules as a capability (Q4).

### 9.4 Function types and closures
- **Function types:** `fn(A) -> R`, `fn(A) -> R fails E`, and `fn(A) -> R with E`, where `E` is an effect variable.
- **A closure's type** records the error it can fail with. Capturing a capability does not change the type; what a closure may capture is limited by its lifetime (§6.7). `proviso query effects` reports both (Q3).

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
let sizes = names.map(|n| dir.size(n) else 0)                   // E = no failure; capturing dir is allowed
```
- **Where marking happens.** Marking happens where `E` is concrete, at the outer call site.
- **No mixing.** A function with `with E` may not also declare its own `fails` (Q2).

### 9.6 Fakes
- **Writing a fake.** Implement the interface (`impl Dir for MemDir { … }`), then wrap a value as a capability with `Dir.of(x)`. The result carries every permission and narrows like any other capability.
- **Standard fakes.** `std.test` provides `MemDir`, `FakeClock`, `FakeNet` and `SeededRandom`. Their constructors return capabilities directly.

### 9.7 debug
`debug(x, …)` writes debug representations, with the source location, to the debug stream. It needs no capability, and `proviso build --release` rejects it.

### 9.8 Replay
All external observations pass through capabilities, and all scheduling choices happen at channel and join points and where cancellation is delivered (§11). So `proviso run --record` can log every capability result and scheduling choice, and `proviso replay <run>` re-executes the run deterministically. Calling an `extern` that is not `pure` makes the run non-replayable unless the extern is wrapped as a capability. A recording run reports when that happens (§13, T5).

## 10. Resources

```proviso
pub resource record Txn { conn: Conn }
impl Abandon for Txn {
    fn abandon(take self) { self.conn.rollback_quietly() }  // cannot fail
}
```
Every resource type implements `Abandon`.

1. **Consumed exactly once.** A resource value must be consumed exactly once: passed as `take`, or used by a `take self` method such as `commit` or `close`. Resources cannot be copied.
2. **On a normal exit**, every resource in scope must already be consumed, or it is a compile error.
3. **On a failure exit**, whether `fail`, a `try` that propagates, a defect, or cancellation, unconsumed resources are abandoned in reverse order of acquisition. Cancellation is masked while `abandon` runs.
4. **Storage.** Resources can be stored only in `resource record`s.

Scoped helpers are ordinary functions with non-escaping closures:

```proviso
pub fn rename_user(db: Db[write], id: UserId, name: Text) fails DbError
    requires not name.is_empty()       // callers must establish this; it discharges User.name
{
    try db.transaction(|tx| {          // commits on normal exit, rolls back on failure
        let user = try tx.get(id)
        try tx.put(id: id, user: user.with(name: name))
    })                                 // tx cannot escape: non-escaping closure, resource type
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
1. **No shared mutable memory.** A `scope` waits for all its tasks; no task outlives its scope.
2. **Captures.** `spawn` takes a `scoped` closure (§6.7). It captures values by copy and capabilities as borrows, which is safe because the scope outlives its tasks. It cannot capture a `var` mutably.
3. **Communication** goes through `Channel[T]`, which is bounded and carries values (Q15).
4. **Failure.** The first task to fail or hit a defect cancels its siblings. The scope waits for them, then fails with that first error, or propagates that first defect as a defect. The others are recorded in the trace.
5. **Cancellation** is cooperative, and it is not an error: `else`, `attempt` and `supervise` cannot catch it. It is delivered at capability calls, channel operations, `join` and `checkpoint()`. A cancelled task exits through the failure path, so its resources are abandoned.
6. **Determinism.** Data races are impossible. The only nondeterminism is ordering at channel and join points and where cancellation is delivered. `--record` captures both, and `proviso test --schedules N` explores seeded orderings.
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
- **Arithmetic** is IEEE-754, with no fast-math and no implicit fused multiply-add (`x.mul_add(factor: y, addend: z)` is explicit). Results are reproducible across platforms.
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
- **Stable codes.** Diagnostic codes are stable.
- **No cascades.** All errors are reported at once, and an error poisons only its dependents.
- **Broken code.** Queries and edits work on code that does not compile. An answer that depends on broken parts carries `"partial": true` (T1).
- **Locations.** Each location is given two ways: `file:line:col`, and a symbol anchor such as `users.parse_user+8` (line 8 of the item). The anchor stays stable when other items are edited (T3).
- **Revisions.** Every top-level item has a revision hash, which structured edits use (T2).

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
| `proviso fmt` | canonical format |

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

- **Package files.** `proviso.toml` declares the package name, `lang = "0.2"` and the dependencies. `proviso.lock` pins dependencies by content hash.
- **Standard library.** It ships with the toolchain, and `proviso sig std.text` describes the installed version, not a remembered one.
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
    authority     dir: read, not kept                                    [type]
    on failure    no inout parameters; no external writes possible       [type]
    defects       none unproven                                          [verified]

pub fn parse_user(line: Text, line_no: Int) -> User fails LoadError              rev 44b0c7
    authority     none                                                   [type]
    examples      2 passing, cached                                      [tested]
    defects       none unproven                                          [verified]
```
