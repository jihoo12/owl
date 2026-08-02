# Owl Proof Assistant -- Language Reference Manual

Owl is a proof assistant based on cubical type theory. It supports dependent
types, path types, higher inductive types, univalence, and an interactive
tactic mode. This document describes the complete language.

---

## 1. Lexical Structure

### Comments

Line comments begin with `--` and extend to the end of the line:

```
-- this is a comment
def x : Nat := zero  -- inline comment
```

### Identifiers

Identifiers start with a letter or underscore and continue with letters,
digits, underscores, or primes:

```
x  foo  bar'  _hidden  Nat  myVar2
```

### Keywords

The following words are reserved and cannot be used as variable names:

| Keyword       | Purpose                                    |
| ------------- | ------------------------------------------ |
| `def`         | Define a new constant                      |
| `inductive`   | Declare an inductive datatype              |
| `record`      | Declare a record type (sugar for inductive) |
| `field`       | Field declaration in a record              |
| `where`       | Begin constructor list in datatype         |
| `import`      | Import definitions from another file       |
| `fun`         | Lambda abstraction                         |
| `let`         | Local let binding                          |
| `in`          | End of let binding scope                   |
| `by`          | Enter tactic mode                          |
| `exact`       | Tactic: provide a complete proof term      |
| `intro`       | Tactic: introduce Pi-type binders          |
| `apply`       | Tactic: apply a function to the goal       |
| `assumption`  | Tactic: use a hypothesis from context      |
| `reflexivity` | Tactic: prove reflexive path               |
| `symmetry`    | Tactic: flip path goal endpoints           |
| `split`       | Tactic: prove a Sigma-type pair            |
| `constructor` | Tactic: apply a constructor of goal type   |
| `destruct`    | Tactic: case-split on a hypothesis         |
| `transitivity`| Tactic: chain path equalities              |
| `compute`     | Tactic: normalize the goal type            |
| `trivial`     | Tactic: prove trivial goals automatically  |
| `match`       | Pattern matching / elimination             |
| `return`      | Annotate match return type                 |
| `with`        | Match cases / mutual datatypes separator   |
| `Type`        | Alias for universe `U0`                    |
| `Prop`        | Impredicative proposition universe (U0)   |
| `SSet`        | Strict set universe (U1)                   |
| `lift`        | Lift a value into a higher universe        |
| `lower`       | Lower a value from a higher universe       |
| `Path`        | Path type former                           |
| `PathP`       | Dependent path type (type family required) |
| `hcomp`       | Homogeneous composition                    |
| `comp`        | Heterogeneous composition                  |
| `fill`        | Dependent fill (heterogeneous)             |
| `hfill`       | Homogeneous fill                           |
| `Equiv`       | Equivalence type                           |
| `mkEquiv`     | Construct an equivalence                   |
| `Partial`     | Partial element type (keyword syntax)      |
| `Glue`        | Glue type                                  |
| `glue`        | Glue element introduction                  |
| `unglue`      | Glue element elimination                   |
| `fst`         | First projection from a pair               |
| `snd`         | Second projection from a pair              |
| `ua`          | Univalence axiom                           |
| `transport`   | Transport along a path                     |
| `equivFwd`    | Apply forward map of an equivalence        |
| `forall` / `∀` | Dependent function type former          |
| `Σ`           | Dependent pair type former (Unicode only)  |
| `I` / `𝕀`     | Cubical interval type                      |
| `Delay`       | Coinductive delay type former              |
| `Next`        | Coinductive delay constructor              |
| `Force`       | Coinductive delay destructor               |
| `by_wf`       | Well-founded recursion annotation          |
| `as`          | As-pattern in match cases (contextual)     |

### Symbols and Operators

| Symbol    | Meaning                            | Associativity |
| --------- | ---------------------------------- | ------------- |
| `->`      | Non-dependent function type        | right         |
| `=>`      | Lambda arrow                       | --            |
| `:=`      | Definition body separator          | --            |
| `*` / `x` | Non-dependent product (Sigma) type | right         |
| `@`       | Path/cell application               | left          |
| `/\`      | Interval meet (conjunction)        | right         |
| `\/`      | Interval join (disjunction)        | right         |
| `~`       | Interval negation                  | prefix        |
| `<i>`     | Path lambda (binds interval var)   | --            |
| `[_ \| _]`   | Partial element type (bracket)     | --            |
| `,`       | Pair separator / tactic separator  | --            |
| `:`       | Type annotation                    | --            |
| `;`       | Tactic separator                   | --            |
| `\|`      | Match case separator               | --            |
| `?`       | Hole prefix (`?name` / `?`)        | prefix        |

### Interval Literals

| Literal | Meaning            |
| ------- | ------------------ |
| `i0`    | Left endpoint (0)  |
| `i1`    | Right endpoint (1) |
| `0`     | Literal integer 0, also parsed as `i0` |
| `1`     | Literal integer 1, also parsed as `i1` |

---

## 2. Core Types

Owl is a dependently-typed language. Every expression is either a term or a
type. Types are themselves terms.

### Universes

```
U0  U1  U2  ...
Type          -- alias for U0
Prop          -- impredicative proposition universe, lives in U0
SSet          -- strict set universe, lives in U1
```

Universes are stratified to avoid paradoxes. Each universe contains the types
of the previous level:

```
U0 : U1 : U2 : ...
```

**Cumulativity**: if `n <= m`, then `U_n` is a subtype of `U_m`.

Cumulativity extends structurally to the type formers:

- **Pi (dependent functions)** — contravariant in the domain, covariant in the
  codomain: `Pi(x : A). B ≤ Pi(x : A'). B'` when `A' ≤ A` and `B ≤ B'`.
  For example, a function quantified over `A : U1` is usable wherever a
  function quantified over `A : U0` is expected.
- **Sigma (dependent pairs)** — covariant in both components:
  `Sigma(x : A). B ≤ Sigma(x : A'). B'` when `A ≤ A'` and `B ≤ B'`.
- **Inductive types / records** — covariant in the parameters *only when the
  parameter is covariant in the datatype*: `T ps ≤ T ps'` requires `ps_i ≤ ps'_i`
  for every parameter `i` whose occurrences in the constructor argument types
  are all positive.  Parameters are analyzed for variance (positive, negative,
  or mixed occurrences, tracked through nested datatype applications and
  mutual definitions):
  - covariant parameter → `ps_i ≤ ps'_i`,
  - contravariant parameter (occurs only in arrow domains) → `ps'_i ≤ ps_i`,
  - invariant parameter (occurs both positively and negatively) → `ps_i == ps'_i`.
  Since records desugar to single-constructor inductives with all-positive
  field occurrences, this gives record cumulativity: a record holding a value
  at `U0` can be used where the same record holding it at `U1` is expected
  (e.g. via record update).  A datatype whose parameter occurs negatively,
  such as `data Bad (A) where | mkb : (A -> Nat) -> Bad A`, is *not*
  covariant in `A`, so `Bad U0 ≤ Bad U1` is rejected.
- **Path / Partial** — covariant in the type components; Partial additionally
  requires the inferred cofibration to imply the expected one.

Subtyping is reflexive: identical terms are always subtypes of themselves,
which is what lets the recursive checks above close over bound variables and
neutral terms that appear in dependent positions. See
`examples/cumulativity_sigma_pi.owl` for worked examples.

**Prop** is an impredicative universe for propositions. `Prop : U0`, and
`Pi(x:Prop). Prop : Prop` (impredicativity). Prop types can be used as
motives in eliminators.

**SSet** is a strict set universe at level 1. It is predicative: closed under
Pi, Sigma, and Path at level 1.

### Universe Lifting and Lowering

```
lift A        -- lift type A from U_n to U_{max(n, m)}
lower a       -- lower a value of a lifted type back down
```

Universe lifting (`lift`) embeds a type into a higher universe. This is
needed when cumulativity is not sufficient — for example, when a function
requires all arguments at the same universe level:

```
-- Nat : U0, but we need it at U1 for a specific context
def lifted_nat : lift Nat := lift zero
```

`lift A : U_{max(n,m)}` when `A : U_n`. `lower` reverses the embedding:
`lower (lift x) = x`.

### Pi Types (Dependent Functions)

```
forall (x : A), B        -- dependent
A -> B                   -- non-dependent (shorthand)
```

The codomain `B` may reference the argument `x`. Non-dependent function
types are sugar for `forall (_ : A), B`.

### Sigma Types (Dependent Pairs)

```
Σ (x : A), B         -- dependent (use Unicode Σ)
A * B                -- non-dependent (shorthand)
```

Note: The Sigma type former requires the Unicode character `Σ`, not the ASCII
string `Sigma`.

Pairs are written `(a , b)`. Projections use `fst` and `snd`.

### Path Types

```
Path A u v
```

A path from `u` to `v` in type `A`. Path types are the cubical core
of equality: `Path A u v` is the type of proofs that `u` equals `v` in `A`.

### Partial Elements (Cubical Subtypes)

```
[_ | phi] A          -- bracket syntax
Partial phi A        -- keyword syntax
```

Partial elements restrict a type to a face. `[_ | phi] A` is the type of
elements of `A` that are defined when `phi` is true. This is fundamental
for constructing Glue types and defining cubical subtyping.

- `phi` is an interval expression (face restriction)
- `A` is the base type
- When `phi` is always true (i1), `[_ | i1] A` reduces to `A`
- When `phi` is always false (i0), `[_ | i0] A` has no inhabitants

**Type inference**: `[_ | phi] A : U_n` when `A : U_n`.

**Cofibration subtyping**: `[_ | phi] A` is a subtype of `[_ | psi] A` when
`phi <= psi` (i.e., `phi` implies `psi`). This is checked via DNF face
implication. For example, `[_ | i1 /\ i0] A` is a subtype of `[_ | i1] A`
because `i1 /\ i0` implies `i1`.

**Example:**

```
-- A partial element defined on face i1
def partial_one : [_ | i1] Nat := suc zero
```

### System Types

```
[phi => A, psi => B]    -- system type
```

System types represent partial functions — types that map faces to types.
Each entry `phi => A` specifies a face condition `phi` and a type `A` that
applies when that face is active. System types are first-class types that
live in a universe.

**Type inference**: `[phi => A, psi => B] : U_n` when all `A_i : U_n` and
all faces are interval expressions. The system must be **coherent**: for
any two entries, their types must agree on the intersection of their faces.
This is checked via `dnf_meet`.

**Example:**

```
-- A system type over two faces
def sys_type : [i1 => Nat, i0 => Nat] := [i1 => Nat, i0 => Nat]
```

### Equivalence Type

```
Equiv A B
```

The type of equivalences between `A` and `B`. Constructed with `mkEquiv`.

### The Interval

```
I
```

The cubical interval type, with endpoints `i0` (0) and `i1` (1).
Interval expressions support meet (`/\`), join (`\/`), and negation (`~`).

### Datatypes

User-defined types declared with `inductive`. Referenced by name (e.g. `Nat`).

### Records

```
record Name (params...) where
  field name1 : Type1
  field name2 : Type2
```

Records are syntactic sugar for single-constructor inductives. A record
declaration `record R (p : P) where field f : T` desugars to:

```
inductive R (p : P) where
  | mkR : T -> R p
```

The constructor is automatically named `mk` followed by the record name
(e.g. `mkPair`, `mkPoint`).

**Field access** uses dot notation: `r.field`. Chained projections work:
`r.field1.field2`.

**Record update** uses `{ field = value }` syntax:

```
r { field = new_value }
```

This produces a new record with the specified fields replaced. Multiple
fields can be updated at once: `r { f1 = v1, f2 = v2 }`. Fields not mentioned
retain their original values.

**Example:**

```
record Pair (A : Type) (B : Type) where
  field fst : A
  field snd : B

def swap : ∀ A B, Pair A B -> Pair B A :=
  fun A B p => mkPair p.snd p.fst
```

This is equivalent to:

```
inductive Pair (A : Type) (B : Type) where
  | mkPair : A -> B -> Pair A B

def swap : ∀ A B, Pair A B -> Pair B A :=
  fun A B p => mkPair (p.snd) (p.fst)
```

---

## 3. Definitions

### Syntax

```
def name : Type := value
def name : Type := by tactic1; tactic2
```

Definitions bind a name to a typed value. The value is checked against the
type annotation. Definitions are **recursive** -- a definition may reference
itself and all earlier definitions by name.

### Examples

```
def id : forall (A : U0), A -> A := fun A x => x

def const : ∀ (A B : U0), A -> B -> A := fun A B a b => a

def double : Nat -> Nat := fun n => add n n
```

### Tactic Definitions

A definition body can be written as a tactic block instead of an explicit
term:

```
def id : forall (A : U0), A -> A := by intro A x; exact x
```

The tactic block must be preceded by the full type annotation so that the
tactics know what goal to solve. See [Tactic Mode](#9-tactic-mode).

### Holes (incomplete proofs)

A **hole** is an incomplete proof term, written `?name`, `?`, or `_`. Holes
are placeholders that Owl either solves automatically or reports as errors:

```
def answer : ?ty := zero      -- ?ty is solved to Nat by unification
def next : Nat := suc zero    -- a complete definition
```

- `?name` is a named hole; `?` and `_` are anonymous holes. Anonymous holes
  are numbered in error messages (`?_0`, `?_1`, ...) so they can be
  distinguished.
- A hole in a **type annotation** is solved by unification when the body
  constrains it (`def x : ?ty := zero` gives `x : Nat`).
- A hole in a **value position** is solved when the type checker compares it
  against a concrete type; otherwise it must be filled manually.

A definition that still contains an unsolved hole is **rejected**. Owl
reports every unsolved hole together with its expected type:

```
owl: type error:
  Unsolved holes remain in this definition:
    ?n : Nat
  (fill each hole or provide a complete proof before the definition is accepted)
```

This lets you sketch a proof with holes and fill them incrementally, knowing
exactly which goals remain open.

### Entry Point

When Owl is run on a file, it normalizes the definition named `main` (or
falls back to the last definition). The result is printed as:

```
main : Type = normalized_value
```

---

## 4. Lambda Abstraction

### Syntax

```
fun x => body               -- single binder
fun x y z => body           -- multiple binders
fun (x : A) => body         -- with type annotation (annotation ignored in core)
```

### Semantics

`fun x => body` constructs a function. The variable `x` is bound in `body`
with de Bruijn index 0. Multiple binders are sugar for nested lambdas:

```
fun x y => body    =    fun x => (fun y => body)
```

### Examples

```
fun n => match n return Nat with | zero => n | suc k => suc (add k n)

fun A x => x

fun (x : Nat) (y : Nat) => add x y
```

---

## 5. Let Bindings

### Syntax

```
let x := value in body
let x : Type := value in body    -- type annotation is optional
```

### Semantics

Let bindings are syntactic sugar for function application:

```
let x := value in body    =    (fun x => body) value
```

The type annotation is accepted for readability but discarded in the core
representation.

---

## 6. Datatypes

### Ordinary Inductive Types

```
inductive Nat where
  | zero : Nat
  | suc : Nat -> Nat
```

A datatype declaration specifies:
1. The **name** of the type (`Nat`)
2. An optional **universe annotation** (`: U_n`)
3. A list of **constructors**, each with a name and argument types

### Universe Annotation

The universe level can be specified explicitly:

```
data D : U2 where
  | con : D -> D
```

If omitted, the level is inferred as the maximum over all constructor argument
universe levels.

### Recursive Datatypes

A constructor may refer to the type being defined:

```
inductive Nat where
  | zero : Nat
  | suc : Nat -> Nat           -- Nat appears as an argument (positive)
```

### Parameterized Datatypes

A datatype can be **parameterized** by declaring binders between the name and
`where`. Parameters appear in the return type of every constructor and are
applied when the datatype is used:

```
inductive List (A : U0) where
  | nil : List A
  | cons : A -> List A -> List A
```

Parameters are written as `(A : Type)` after the datatype name. Inside
constructor types, the parameter `A` is available by name. When the datatype
is referenced elsewhere, parameters are passed as arguments:

```
List Nat          -- parameterized with A = Nat
TData "List" [Nat]   -- internal representation
```

#### Multi-Parameter Datatypes

```
inductive Pair (A : U0) (B : U0) where
  | mkPair : A -> B -> Pair A B
```

#### Parameterized Recursive Types

Parameters can be used alongside recursion:

```
inductive List (A : U0) where
  | nil : List A
  | cons : A -> List A -> List A

inductive Tree (A : U0) where
  | leaf : Tree A
  | node : Tree A -> A -> Tree A -> Tree A
```

### Higher Inductive Types (HITs)

Higher inductive types extend ordinary inductive types with **path
constructors** — constructors that produce paths rather than points. Path
constructors specify boundary conditions (face terms) for `i0` and `i1`.

#### Syntax

```
inductive Name where
  | con : ... [ face0 , face1 ]
```

The `[ face0 , face1 ]` after a constructor declares it as a path
constructor. `face0` is the value at `i0` and `face1` is the value at `i1`.
Both are terms that may reference the constructor's ordinary arguments.

#### Example: Circle

```
inductive S1 where
  | base : S1
  | loop : S1 [ base , base ]
```

`loop` has no ordinary arguments and produces a path from `base` to `base`.

#### Example: Truncation

Truncation is a parameterized HIT that collapses all paths:

```
inductive Trunc (A : U0) where
  | inc : A -> Trunc A
  | trunc : A -> A -> Trunc A [ inc trunc_0 , inc trunc_1 ]
```

`trunc` is a path constructor: it takes two arguments and produces a path
between `inc trunc_0` and `inc trunc_1`, asserting that all points in
`Trunc A` are equal. The face terms `inc trunc_0` and `inc trunc_1` reference
the constructor's arguments (the first and second `A` values).

#### Example: Pushout (Double Pushout)

```
inductive Pushout (A : U0) (B : U0) (C : U0) where
  | left : A -> Pushout A B C
  | right : B -> Pushout A B C
  | glue : C -> Pushout A B C [ left glue_0 , right glue_0 ]
```

`glue` is a path constructor connecting `left c` to `right c` for each
`c : C`. The face terms `left glue_0` and `right glue_0` reference the
constructor's first argument.

#### Example: Suspension

```
inductive Susp (A : U0) where
  | north : Susp A
  | south : Susp A
  | merid : A -> Susp A [ north , south ]
```

`merid` is a path constructor connecting `north` to `south` for each
element `a : A`.

#### Square Constructors (2D HIT Cells)

Square constructors extend path constructors with **two-dimensional cells**.
They specify a surface whose boundary is determined by four face terms.

##### Syntax

```
con : T [[ face_i0 , face_i1 , face_j0 , face_j1 ]]
```

The four face terms define the boundary of a square:
- `face_i0`, `face_i1`: the s-boundaries at r=0 and r=1 (points of the base type)
- `face_j0`, `face_j1`: the r-boundaries at s=0 and s=1 (paths connecting face_i0 to face_i1)

Face terms can reference the constructor's ordinary arguments via de Bruijn
indices, and the two interval variables r, s are implicitly bound.

##### Example: Torus

The torus is the canonical example of a square constructor:

```
inductive Torus where
  | base : Torus
  | line1 : Torus [ base , base ]
  | line2 : Torus [ base , base ]
  | square : Torus [[ base , base , line2 , line2 ]]
```

Here `square` has:
- `face_i0 = base` (at r=0, the square's s-boundary is the constant base)
- `face_i1 = base` (at r=1, the square's s-boundary is also base)
- `face_j0 = line2` (at s=0, the square's r-boundary is line2)
- `face_j1 = line2` (at s=1, the square's r-boundary is also line2)

##### Path Application on Square Constructors

Square constructors are applied with two interval arguments:

```
square @ r @ s     -- apply square at interval points r and s
```

At concrete endpoints:

```
square @ i0 @ i0  =  base     -- face_i0 at s=0
square @ i0 @ i1  =  base     -- face_i0 at s=1
square @ i1 @ i0  =  base     -- face_i1 at s=0
square @ i1 @ i1  =  base     -- face_i1 at s=1
```

##### Elimination of Square Constructors

When pattern-matching on a type with a square constructor, the case body
must be a **double path lambda** `<r> <s> body` where `r` and `s` are the
two interval variables. The body type is a nested PathP:

```
PathP (<r> PathP (<s> T) face_i0 face_i1) face_j0 face_j1
```

**Example: Identity function on Torus**

```
def id_torus : Torus -> Torus :=
  fun x => match x return Torus with
  | base => base
  | line1 i => <j> line1 @ j
  | line2 j => <k> line2 @ k
  | square r s => <i> <j> square @ i @ j
```

The square case body `<i> <j> square @ i @ j` constructs a surface that
applies `square` at the two fresh interval variables, producing a value of
type `Torus` for each pair of interval points.

#### N-Dimensional Cell Constructors (3D and Higher)

Cell constructors generalize square constructors to arbitrary dimension.
A cell constructor of dimension *n* specifies 2*n* face terms, one for
each boundary face of the *n*-dimensional cell.

##### Syntax

```
con : T [[[ face_10 , face_11 , face_20 , face_21 , ... , face_n0 , face_n1 ]]]
```

Bracket depth determines the dimension: `[[[` is dimension 3 (a cube),
`[[[[` is dimension 4, and so on. Face terms are ordered innermost to
outermost:

- `face_10, face_11`: boundary at innermost interval r_1 = 0 and r_1 = 1
- `face_20, face_21`: boundary at r_2 = 0 and r_2 = 1
- ...
- `face_n0, face_n1`: boundary at outermost interval r_n = 0 and r_n = 1

The inferred type is a nested PathP:

```
PathP (<r_1> PathP (<r_2> ... PathP (<r_n> T) face_10 face_11) ... face_{n-1,0} face_{n-1,1}) face_n0 face_n1
```

Face terms can reference the constructor's ordinary arguments via de Bruijn
indices. The *n* interval variables are implicitly bound.

##### Example: 3D Cube Cell

```
inductive Cube where
  | base : Cube
  | line1 : Cube [ base , base ]
  | line2 : Cube [ base , base ]
  | square : Cube [[ base , base , line2 , line2 ]]
  | cube3  : Cube [[[ base , base , line2 , line2 , square , square ]]]
```

`cube3` is a 3-dimensional cell constructor with 6 face terms:
- Innermost boundary (r_1): `base, base`
- Middle boundary (r_2): `line2, line2`
- Outermost boundary (r_3): `square, square`

##### Application on Cell Constructors

Cell constructors are applied with *n* interval arguments:

```
cube3 @ r @ s @ t    -- apply cube3 at three interval points
```

At concrete endpoints, cell constructors reduce to their boundary values:

```
cube3 @ i0 @ i0 @ i0  =  base     -- innermost face at all endpoints
cube3 @ i1 @ i1 @ i1  =  base     -- all faces at i1
cube3 @ i0 @ i1 @ i0  =  base     -- mixed endpoints
```

##### Elimination of Cell Constructors

When pattern-matching on a type with an n-dimensional cell constructor,
the case body must be an *n*-fold path lambda `<r_1> <r_2> ... <r_n> body`.
The body type is a nested PathP:

```
PathP (<r_1> PathP (<r_2> ... PathP (<r_n> T) face_10 face_11) ...) face_n0 face_n1
```

**Example: Identity function on Cube**

```
def id_cube : Cube -> Cube :=
  fun x => match x return Cube with
  | base => base
  | line1 i => <j> line1 @ j
  | line2 j => <k> line2 @ k
  | square r s => <i> <j> square @ i @ j
  | cube3 r s t => <i> <j> <k> cube3 @ i @ j @ k
```

The cube case body `<i> <j> <k> cube3 @ i @ j @ k` constructs a
3-dimensional cell that applies `cube3` at three fresh interval variables.

#### Path Constructor Face Terms

Face terms reference constructor arguments via de Bruijn-like scoping.
Ordinary arguments are bound in order (first argument at highest index),
and face terms can use these arguments:

```
inductive S2 where
  | base2 : S2
  | loop2 : S2 [ base2 , base2 ]
```

Face terms are point-level terms — they can be:
- Simple references: `base`, `north`, `left c`
- Path applications: `inc (f a)` 
- Complex expressions: `suc zero`

### Positivity Requirement

A datatype `D` may only appear **strictly positively** in its own constructor
argument types. This means `D` cannot appear to the left of an arrow in any
constructor's argument type:

```
-- Allowed:
data Nat where | zero : Nat | suc : Nat -> Nat

-- Rejected (D appears as domain):
data Bad where | mk : Bad -> Bad
```

This requirement applies to both ordinary and parameterized datatypes. For
parameterized types, the positivity check examines constructor types after
the parameters are in scope.

### Mutual Inductive Types (Induction-Induction)

Multiple inductive types can be declared simultaneously using the `with`
keyword. Each type's constructors may reference any of the other types in
the same mutual block:

```
inductive even where
  | even_zero : even
  | even_suc : even -> even
with inductive odd where
  | odd_one : odd
  | odd_suc : odd -> odd
```

All types in a mutual block are registered before constructor typechecking,
so **forward references** work: the second type can reference the first.

#### Syntax

```
inductive A where | ... | ...
with inductive B where | ... | ...
[with inductive C where | ... | ...]
```

### Induction-Recursion

An inductive type and a function over it can be defined simultaneously. The
function is defined after the datatype, with the datatype already in scope:

```
inductive Nat where
  | zero : Nat
  | suc : Nat -> Nat
with isZero : Nat -> Nat := fun n =>
  match n return Nat with
  | zero => suc zero
  | suc _ => zero
```

The function can pattern-match on the datatype being defined. After the
declaration, both the datatype and the function are available for use.

#### Syntax

```
inductive D where | ... | ...
with func_name : FuncType := func_body
```

### Structural Recursion Guard

The typechecker enforces that recursive calls in `match`/eliminator cases
follow the **structural recursion guard**: the recursive call must
decrease on a strict subterm of the scrutinee. Specifically, each ordinary
constructor case must pass a case binder (a constructor argument) as the
scrutinee of any recursive call.

```
-- Accepted: recursive call uses subterm m'
def add : Nat -> Nat -> Nat := fun m n =>
  match m return Nat with
  | zero => n
  | suc m' => suc (add m' n)   -- add called with m', a subterm of m

-- Rejected: recursive call uses full m (not a subterm)
def bad : Nat -> Nat := fun m =>
  match m return Nat with
  | zero => zero
  | suc m' => bad m            -- ERROR: m is not a strict subterm
```

### Well-Founded Recursion (`by_wf`)

The `by_wf` annotation on a `def` disables the structural recursion guard
check, allowing the definition to use well-founded recursion. This is
useful when the recursive argument is not a syntactic subterm but the
recursion is still well-founded.

```
def double : Nat -> Nat by_wf := fun n =>
  match n return Nat with
  | zero => zero
  | suc n' => suc (suc (double n'))
  end
```

### Coinduction (`Delay` / `Next` / `Force`)

Owl supports coinductive types via a built-in delay type `Delay A`:

- `Delay A` — the type of delayed computations of type `A`.
- `Next : A -> Delay A` — wraps a value into a delayed computation.
- `Force : Delay A -> A` — forces a delayed computation.

The key beta rule is: `Force (Next x) = x`.

```
def wrap : forall (A : U0), A -> Delay A := fun A x => Next x

def unwrap : forall (A : U0), Delay A -> A := fun A d => Force d

-- Round-trip: Force (Next x) = x
def id_delayed : forall (A : U0), A -> A := fun A x => Force (Next x)
```

`Delay A` lives in the same universe as `A`: if `A : U_n` then `Delay A : U_n`.

---

## 7. Pattern Matching and Elimination

### Syntax

```
match scrutinee return ReturnType with
  | con1 => body1
  | con2 arg1 arg2 => body2
  | con3 arg1 arg2 arg3 => body3
```

The scrutinee can be a bare name (resolved from scope) or an arbitrary term.
The `return` clause specifies the **motive** (dependent return type). The
motive is a function from the matched type to a type family.

### Pattern Variants

Match cases support several pattern forms:

#### Ordinary Patterns

Each case matches a constructor name followed by binders that are bound to
the constructor's arguments:

```
match n return Nat with
  | zero => zero
  | suc m' => suc (suc m')
```

#### Wildcard Pattern

A single underscore `_` as a binder discards the argument:

```
match n return Nat with
  | zero => zero
  | suc _ => zero
```

#### As-Patterns

An as-pattern binds the full constructor value to a name using `as`:

```
match n return Nat with
  | zero => n
  | suc m as x => x       -- x is bound to suc m (the entire value)
```

The as-name is available alongside the constructor's binders. In the example
above, `x` is the full `suc m` value, while `m` is the inner Nat. This is
useful for recursive calls where you need both the original value and its
inner components.

As-patterns can be combined with or-patterns:

```
match n return Nat with
  | zero as x | suc m as x => x
```

#### Record Patterns

Record patterns destructure records by field name using `{ field = binder }`
syntax:

```
record Pair (A : U0) (B : U0) where
  field fst : A
  field snd : B

def swap_pair : ∀ A B, Pair A B -> Pair B A :=
  fun A B p => match p return Pair B A with
    | mkPair { fst = x, snd = y } => mkPair y x
```

Each field specifies a binder that receives that field's value. Field binders
are in order of field declaration. As-patterns may follow the record pattern:

```
  | mkPair { fst = x, snd = y } as p => mkPair p.snd p.fst
```

#### Or-Patterns

Multiple patterns can share the same body using `|`:

```
match n return Nat with
  | zero | suc _ => zero
```

The patterns must match at the same column (indentation). The body is shared;
the binders from the last pattern are used.

### Record Update

Records can be updated using `{ field = value }` syntax on an existing record
expression:

```
def set_fst : ∀ A B, Pair A B -> A -> Pair A B :=
  fun A B p a => p { fst = a }
```

The expression `p { fst = a }` produces a new record with `fst` replaced by
`a` and all other fields unchanged. Multiple fields can be updated:

```
p { fst = a, snd = b }
```

### Elimination Semantics

The match expression is desugared to the core eliminator form:

```
elim[M] { case1 | case2 | ... } scrutinee
```

where `M` is the motive function. Reduction occurs when the scrutinee is a
constructor value: the matching case body is selected and its binders are
substituted with the constructor's arguments.

### Examples

Simple match:

```
match n return Nat with
  | zero => zero
  | suc m' => suc (suc m')
```

Match with dependent return type:

```
match n return Nat with
  | zero => zero
  | suc m' => add m' m'
```

Match with as-pattern:

```
def as_succ_of : Nat -> Nat := fun n =>
  match n return Nat with
  | zero => suc n
  | suc m as x => suc (suc m)
```

---

## 8. Path Types and Cubical Features

Path types are the heart of cubical type theory. They internalize equality
as a type: `Path A u v` is the type of paths from `u` to `v` in `A`.

### Path Lambda (Interval Abstraction)

```
<i> body      -- binds interval variable i in body
```

A path lambda constructs a path by abstracting over the interval variable.
For example:

```
<i> i         -- the identity path (reflexivity)
<i> i0        -- the constant-0 path
```

### Path Application

```
p @ r         -- apply path p at interval point r
```

Applying a path at an interval expression gives a point in the base type.
Boundary reductions:

```
p @ i0 = u      -- when p : Path A u v
p @ i1 = v
```

### Path Application on Path Lambdas

Path application on a path lambda reduces by substitution:

```
(<i> body) @ r   =   body[i := r]
```

### Path Type Formation

```
Path A u v
```

where:
- `A : Type` is the base type
- `u : A` is the left endpoint
- `v : A` is the right endpoint

A proof of `Path A u v` is a path lambda `<i> body` such that:
- `body[i := i0]` equals `u`
- `body[i := i1]` equals `v`

### Dependent Path Type (PathP)

```
PathP A u v
```

`PathP` is syntactic sugar for `Path` that requires the first argument to be
a **type family** (a function from the interval to types). This makes the
intent clear: the path endpoints may live in different fibers of the family.

- `A : I -> Type` is a type family over the interval
- `u : A(i0)` is the left endpoint (in the fiber at i0)
- `v : A(i1)` is the right endpoint (in the fiber at i1)

**Example:**

```
-- Constant family: PathP reduces to Path
def p : PathP (<i> Nat) zero zero := <i> zero

-- A path from zero to suc zero in a dependent setting
def q : PathP (<i> Nat) zero (suc zero) := <i> suc zero
```

Note: `Path A u v` is equivalent to `PathP (<i> A) u v` when `A` is a
constant type. The `Path` keyword accepts either a plain type or a type
family; `PathP` explicitly signals that the first argument is a family.

### Interval Algebra

Interval expressions support:

| Operation | Syntax | Meaning |
| --------- | ------ | ------- |
| Left endpoint | `i0` | 0 |
| Right endpoint | `i1` | 1 |
| Meet | `i /\ j` | Conjunction (min) |
| Join | `i \/ j` | Disjunction (max) |
| Negation | `~i` | Complement (1 - i) |

Interval expressions are evaluated to Disjunctive Normal Form (DNF) for
face restrictions.

### Face Implication

Given two DNF face conditions `a` and `b`, face implication `a ⇒ b` checks
whether `a` logically implies `b`. In DNF, this means: for every cube `ca`
in `a`, there exists a cube `cb` in `b` such that `cb ⊆ ca` (every literal
in `cb` is also in `ca`).

Face implication is used for:
- **Cofibration subtyping**: `[_ | phi] A <= [_ | psi] A` when `phi ⇒ psi`
- **System coherence**: checking that system types agree on overlapping faces
- **Face lattice reasoning**: `i1 ⇒ i0 /\ i1` holds, `i1 /\ i0 ⇒ i0` holds

**Examples:**
- `i1 ⇒ i1` — true (always implies itself)
- `i1 /\ i0 ⇒ i1` — true (conjunction implies its components)
- `i0 ⇒ i1` — true (false implies anything)
- `i1 ⇒ i0` — false (true does not imply false)

### Face Restrictions

Face restrictions are used in homogeneous composition and Glue types.
A face formula is a DNF expression built from interval literals:

```
i0 /\ ~i1       -- i0 is true AND i1 is false
i0 \/ i1        -- i0 is true OR i1 is true
~i0 /\ i1       -- i0 is false AND i1 is true
```

---

## 9. Homogeneous Composition

```
hcomp A [phi => tube, ...] base     -- system syntax (preferred)
hcomp A phi tube base               -- legacy single-face syntax
```

Homogeneous composition composes paths along faces:

- `A` : the type
- `[phi => tube, ...]` : a system of face-tube pairs (separated by `=>`)
- `base : A` the base element

Each system entry `phi => tube` specifies:
- `phi` : a face formula (interval expression)
- `tube : (i : I) -> A` a path (PLam) that agrees with `base` at `i = 0`

### Boundary Reductions

```
hcomp A [phi => tube, ...] base @ i0  =  base
hcomp A [phi => tube, ...] base @ i1  =  tube @ i1   (on face phi)
```

Each tube must satisfy `tube @ 0 = base` on its face.

### Examples

```
-- Single face
hcomp Nat [i1 => <i> suc zero] (suc zero)

-- Multi-face: both tubes match base at i=0
hcomp Nat [i0 => <i> suc zero, i1 => <i> suc zero] (suc zero)

-- Non-trivial faces
hcomp Nat [1 /\ 1 => <i> suc zero] (suc zero)
hcomp Nat [0 \/ 0 => <i> zero] zero
```

---

## 10. Kan Operations (comp, fill, hfill)

Owl implements the three core Kan operations for cubical type theory: `comp`
(heterogeneous composition), `fill` (dependent fill), and `hfill` (homogeneous
fill). These operations generalize `hcomp` to work with type families and
provide canonical path constructors. All three support the multi-face system
syntax `[phi => tube, ...]` as well as the legacy single-face syntax `phi tube`.

### Heterogeneous Composition (`comp`)

```
comp A [phi => tube, ...] base     -- system syntax
comp A phi tube base               -- legacy single-face syntax
```

Heterogeneous composition composes a family of paths along a face `phi`:

- `A : I -> Type` — a type family over the interval
- `phi : I -> Bool` — a face formula (cube/DNF)
- `tube : (i : I) -> A i` — a function providing paths along each face
- `base : A 0` — the base element

**Type**: `A 1`

**Boundary Reductions**:

```
comp A phi tube base @ i0  =  base
comp A phi tube base @ i1  =  tube @ i1
```

When `phi = 1` (always true), `comp` reduces to `tube @ 1`.
When `phi = 0` (always false), `comp` reduces to `base`.

**Decomposition**: `comp` decomposes through Pi and Sigma types:
- Pi: `comp (fun x -> B x) phi tube base = fun x -> comp (B x) phi (fun i -> tube i x) (base x)`
- Sigma: `comp (A * B) phi tube base = (comp A phi (fun i -> fst (tube i)) (fst base), comp B phi (fun i -> snd (tube i)) (snd base))`

### Dependent Fill (`fill`)

```
fill A [phi => tube, ...] base     -- system syntax
fill A phi tube base               -- legacy single-face syntax
```

Dependent fill constructs a path from `base` to `comp A phi tube base`:

- `A : I -> Type` — a type family over the interval
- `phi : I -> Bool` — a face formula (cube/DNF)
- `tube : (i : I) -> A i` — a function providing paths along each face
- `base : A 0` — the base element

**Type**: `Path (fun j -> A j) base (comp A phi tube base)`

**Endpoint Reductions**:

```
fill A phi tube base @ i0  =  base
fill A phi tube base @ i1  =  comp A phi tube base
```

When `phi = 1` (always true), `fill` reduces to `tube`.
When `phi = 0` (always false), `fill` reduces to `fun j -> base`.

### Homogeneous Fill (`hfill`)

```
hfill A [phi => tube, ...] base     -- system syntax
hfill A phi tube base               -- legacy single-face syntax
```

Homogeneous fill constructs a path from `base` to `hcomp A phi tube base`:

- `A : Type` — a constant type (not a family)
- `phi : I -> Bool` — a face formula (cube/DNF)
- `tube : I -> A` — a function providing paths along each face
- `base : A` — the base element

**Type**: `Path A base (hcomp A phi tube base)`

**Endpoint Reductions**:

```
hfill A phi tube base @ i0  =  base
hfill A phi tube base @ i1  =  hcomp A phi tube base
```

When `phi = 1` (always true), `hfill` reduces to `tube`.
When `phi = 0` (always false), `hfill` reduces to `fun j -> base`.

### Examples

```
-- Heterogeneous composition: constant family
def comp_example : Nat :=
  comp Nat 1 (<i> suc zero) (suc zero)

-- Dependent fill: constructs a path
def fill_example : Nat :=
  fill Nat 1 (<i> suc zero) (suc zero) @ i1

-- Homogeneous fill: constructs a path to hcomp
def hfill_example : Nat :=
  hfill Nat 1 (<i> suc zero) (suc zero) @ i1

-- Fill in a function: variable tube
def fill_fn : Nat -> Nat :=
  fun n => fill Nat 1 (<i> n) n @ i1

-- Transport over comp
def transport_comp : Nat :=
  transport (<i> Nat)
    (comp Nat 1 (<i> suc zero) (suc (suc zero)))
```

---

## 11. Glue Types and Univalence

### Glue Types

```
Glue A phi te
```

Glue type construction: `A` is the base type, `phi` is a face restriction,
and `te` provides equivalences on the face where `phi` is true.

When `phi` is false, `Glue A phi te` reduces to `A`.
When `phi` is true, it reduces to the domain of the equivalence.

### Glue Element Introduction

```
glue phi t a
```

Constructs a value of Glue type from:
- `phi` : a face restriction
- `t` : the cap (in the equivalence domain, when `phi` is true)
- `a` : the base (in `A`)

### Glue Element Elimination

```
unglue phi te g
```

Extracts the underlying `A`-component from a Glue-typed value `g`.

### Glue Element β-Reduction

Glue elements reduce at interval endpoints:

| Form | Reduction |
| ----- | --------- |
| `VGlueElem(phi, t, a) @ 0` | `a` (the base component) |
| `VGlueElem(phi, t, a) @ 1` | `t` (the cap component) |

These reductions allow glue elements to be unrolled at the endpoints of the
interval, which is essential for Kan operations and univalence.

### Equivalences

```
Equiv A B
```

The type of equivalences from `A` to `B`. Constructed with:

```
mkEquiv A B f g eta eps
```

where:
- `f : A -> B` (forward map)
- `g : B -> A` (backward map)
- `eta : (a : A) -> Path A a (g (f a))` (retraction homotopy)
- `eps : (b : B) -> Path B (f (g b)) b` (section homotopy)

### Forward Map Application

```
equivFwd e x
```

Apply the forward map of equivalence `e` to `x`. Reduces when `e` is
`mkEquiv`:

```
equivFwd (mkEquiv A B f g eta eps) x  =  f x
```

### Univalence

```
ua e
```

where `e : Equiv A B`. Produces a path in the universe:

```
ua e : Path U A B
```

The univalence axiom is realized as a primitive operation with built-in
reduction rules.

### Transport

```
transport p x
```

where:
- `p : Path U A B` (a type family over the interval)
- `x : A`

Transport moves `x` from type `A` to type `B` along the path `p`.

**Reduction rules**:
- Constant family: `transport (<i> A) x` reduces to `x`
- Univalence: `transport (ua e) x` reduces to `equivFwd e x`
- Pi decomposition: transport through a Pi type produces a lambda
- Path decomposition: transport through a Path type produces a path lambda
- Sigma decomposition: transport through a Sigma type produces a pair

---

## 12. Tactic Mode

Tactic mode provides an interactive way to construct proof terms. A tactic
block appears in a definition body where a term is expected, and **requires
a type annotation** since tactics need to know the goal type.

### Syntax

```
by tactic1; tactic2; tactic3
```

Tactics are separated by semicolons. The block produces a single proof term
that is checked against the declared type.

### Available Tactics

#### `intro`

Introduce one or more Pi-type binders. Each name peels off one `forall` /
function arrow and binds a variable in the context.

```
-- Goal: forall (A : U0), A -> A
-- After: intro A x
--   Context: A : U0, x : A
--   Goal: A

def id : forall (A : U0), A -> A := by intro A x; exact x
```

Multiple names can be introduced at once:

```
by intro A B x     -- equivalent to: intro A; intro B; intro x
```

The names introduced by `intro` become bound variables that later tactics
can reference.

#### `exact`

Provide a complete proof term for the current goal. The term is type-checked
against the goal type in the accumulated context (from prior `intro` tactics).

```
-- After intro A x, the goal is A.
-- exact x provides the variable x (de Bruijn index 0).

def id : forall (A : U0), A -> A := by intro A x; exact x
```

#### `assumption`

Search the context for a hypothesis whose type matches the goal. Uses
definitional equality (up to eta-expansion) for matching.

```
def id_nat : Nat -> Nat := by intro x; assumption
```

#### `apply`

Apply a function to the current goal. The function must have a Pi type whose
codomain matches (or is definitionally equal to) the goal. The domain becomes
the new subgoal. The function must be a named definition (bare lambdas without
type annotations cannot be inferred by the type checker).

```
-- Goal: Nat
-- apply id_nat_fn  where  id_nat_fn : Nat -> Nat, codomain is Nat
-- New goal: Nat

def id_nat_fn : Nat -> Nat := fun x => x

def apply_test : Nat -> Nat :=
  by intro x; apply id_nat_fn; exact x
```

When multiple arguments are needed, chain `apply` tactics:

```
def add_one : Nat -> Nat := fun n => suc n

def compose_test : Nat -> Nat :=
  by intro x; apply add_one; apply add_one; exact x
```

`apply` also works with previously defined tactic proofs:

```
def id_nat : Nat -> Nat := by intro x; assumption

def test : Nat -> Nat := by intro x; apply id_nat; exact x
```

The function term can reference earlier definitions and hypotheses available
in the tactic context at the time of the `apply` tactic.

#### `reflexivity`

Prove a reflexive path. When the goal is `Path A u v` and `u` and `v` are
definitionally equal, `reflexivity` produces the constant path `<i> u`.

```
-- Goal: Path Nat zero zero
-- reflexivity succeeds because zero = zero

def refl_zero : Path Nat zero zero := by reflexivity
```

#### `symmetry`

Flip the endpoints of a path goal. When the goal is `Path A u v`, symmetry
changes it to `Path A v u`.

```
-- Goal: Path Nat zero zero
-- After symmetry: Path Nat zero zero (same in this case)

def sym_test : Path Nat zero zero := by symmetry; reflexivity
```

#### `split`

Prove a Sigma type (pair type) by providing each component separately.
When the goal is `Sigma (x : A), B` (or `A * B`), split changes the goal
to `A` (the first component). After the first component is proved, the goal
becomes `B` (possibly substituted with the first component).

```
-- Goal: Nat * Nat
-- After split: goal becomes Nat (first component)
-- After exact (suc zero): goal becomes Nat (second component)
-- After exact zero: done, produces (suc zero , zero)

def pair : Nat * Nat := by split; exact (suc zero); exact zero
```

Projections use `fst` and `snd`:

```
def pair : Nat * Nat := by split; exact (suc zero); exact zero
def first : Nat := fst pair    -- evaluates to 1
```

#### `constructor`

Apply a constructor of the goal datatype. When the goal is an inductive type,
automatically applies a constructor, creating subgoals for each argument.

```
-- Goal: Nat
-- constructor picks 'zero' (first constructor, zero args)
-- Result: zero

def my_zero : Nat := by constructor
```

Specify a constructor by name:

```
-- constructor suc applies the 'suc' constructor, creating a subgoal for its Nat argument
-- exact zero proves that argument

def my_one : Nat := by constructor suc; exact zero
def my_two : Nat := by constructor suc; exact (suc zero)
```

#### `destruct`

Case-split on a hypothesis of an inductive type. Creates one subgoal per
constructor case, with the constructor's arguments added to the context.

```
inductive Bool where
  | true : Bool
  | false : Bool

-- After intro b, destruct b creates two subgoals:
--   Case true: goal is Bool, context is empty
--   Case false: goal is Bool, context is empty

def neg : Bool -> Bool :=
  by intro b; destruct b; exact false; exact true
```

Each case body is proved in sequence. The tactic engine automatically builds
the eliminator (match expression) from the case bodies.

#### `transitivity`

Split a path equality goal into two subgoals via an intermediate point.
When the goal is `Path A x z`, creates two subgoals: prove `Path A x y` and
prove `Path A y z` for a fresh intermediate point `y`.

```
-- Goal: Path Nat x z
-- After transitivity:
--   Subgoal 1: Path Nat x _trans_y  (prove a path from x to some y)
--   Subgoal 2: Path Nat _trans_y z  (prove a path from that y to z)

-- Note: transitivity requires a HIT with path constructors to be fully useful.
-- For Nat, it still works for reflexive paths.
```

#### `compute`

Normalize the current goal type in place. This does not produce a proof term;
it simplifies the goal for easier reasoning.

```
-- Normalizes the goal before proving it
def computed : Nat := by compute; exact (fun x => x) zero
```

#### `trivial`

Prove trivial goals automatically. Succeeds when:
- The goal is a path `Path A u v` with `u` and `v` definitionally equal
  (produces `reflexivity`)
- The goal is an inductive type with a zero-argument constructor
  (applies that constructor)

```
def trivial_path : Path Nat zero zero := by trivial
def trivial_nat : Nat := by trivial    -- applies 'zero'
```

### Example: Multi-Step Tactic Proof

```
def const : forall (A : U0), forall (B : U0), A -> B -> A :=
  by intro A B a b; exact a
```

Step by step:
1. `intro A` -- goal becomes `forall (B : U0), A -> B -> A`, context: `A : U0`
2. `intro B` -- goal becomes `A -> B -> A`, context: `A : U0, B : U0`
3. `intro a` -- goal becomes `B -> A`, context: `A : U0, B : U0, a : A`
4. `intro b` -- goal becomes `A`, context: `A : U0, B : U0, a : A, b : B`
5. `exact a` -- provides `a` (de Bruijn index 1 in the 4-element context)
   which has type `A`, matching the goal

The resulting core term is:

```
fun A B a b => a
```

---

## 13. Imports and Modules

### Import Syntax

```
import "relative/path/to/file.owl"
```

Imports read and process another Owl file, making all its definitions and
datatypes available in the current file. Paths are relative to the importing
file's directory.

### How Imports Work

1. The imported file is processed recursively (including its own imports)
2. All definitions and datatypes from the imported file are merged into the
   current environment
3. Subsequent declarations in the current file can reference imported names
4. Circular imports are detected and rejected with an error

### Example

File `nat.owl`:
```
inductive Nat where
  | zero : Nat
  | suc : Nat -> Nat

def add : Nat -> Nat -> Nat := fun m n =>
  match m return Nat with
  | zero => n
  | suc m' => suc (add m' n)
```

File `main.owl`:
```
import "nat.owl"

def four : Nat := add (suc (suc zero)) (suc (suc zero))

def main : Nat := four
```

Each file is processed only once, even if imported multiple times from
different paths (deduplication by canonical path).

---

## 14. Evaluation and Normalization

Owl uses **Normalisation by Evaluation (NbE)** to compute with terms.

### Strategy

1. **Evaluate** the term into a semantic domain (Values)
2. **Quote** the value back into a syntactic term (normal form)

This approach correctly handles variable binding (via closures) and ensures
strong normalisation for the core calculus.

### Environment Sharing

Evaluation environments use a persistent `Scope` type — an `Rc`-linked chain
of value segments — instead of copying `Vec<Value>` at every binder. This
makes `extend` (adding a single innermost binding) O(1) rather than O(n),
and `clone` shares the existing segment chain via reference counting.
Closure application uses `Scope::extend` (one allocation) instead of
`vec![v] + extend_from_slice` (two allocations plus a full copy of the
existing environment).

### Global Definitions in Normalization

When a term is normalized in the presence of global definitions (the
`nbe_eval_ctx` path used by equality checking), the first `ctx_len` de Bruijn
indices are treated as local binders and everything below them resolves to
global definitions:

- **Local binders** are placed in the evaluation environment as neutral
  variables.
- **Global references** are kept *outside* the environment and resolve
  through the global definition value vector via the index formula
  `global_offset + (i - env.len())`.

Keeping globals out of the environment is load-bearing for termination: a
stuck eliminator created during evaluation captures the environment, and when
it is quoted (`quote_case_body`) the raw global references inside its case
bodies are re-anchored as references *below the quoting frame* instead of
being inlined. If globals were placed in the environment, those references
would land inside `env.len()` and be inlined by re-evaluation — re-opening
recursive definitions (e.g. `add`'s case body calling `add`) on every
normalization pass. That produced unbounded term growth that eventually
exhausted eta-equality fuel (`EtaFuelExhausted`) when comparing two stuck
eliminators that differed only in inlining depth. With globals kept out of the
environment, normalization is **idempotent**: quoting a term twice yields the
same normal form.

### Beta Reduction

```
(fun x => body) arg   =   body[x := arg]
```

### Path Application

```
(<i> body) @ r   =   body[i := r]
```

### Projection

```
fst (a , b)   =   a
snd (a , b)   =   b
```

### Eliminator

When the scrutinee is a constructor, the matching case body is selected and
the constructor's arguments are substituted for the binders.

### Transport Reductions

| Form | Reduction |
| ----- | --------- |
| `transport (<i> A) x` | `x` (constant family) |
| `transport (ua e) x` | `equivFwd e x` |
| `transport p x` (Pi type) | `fun arg => transport (...) (x arg)` |
| `transport p x` (Path type) | Path lambda over transported body |
| `transport p x` (Sigma type) | Pair of transported components |
| `transport p x` (Data type) | Each constructor argument transported through substituted type |
| `transport p x` (PCon) | Point constructor with transported arguments |
| `transport p x` (SqCon) | Square constructor with transported arguments |
| `transport p x` (CellCon) | n-dimensional cell constructor with transported arguments |
| `transport (<i> TLift A m) (lift x)` | `lift (transport (<i> A) x)` (unwrap, transport inner, re-wrap) |
| `transport (<i> TLower A) (lower x)` | `lower (transport (<i> A) x)` (unwrap, transport inner, re-wrap) |

### Kan Operation Reductions

| Form | Condition | Reduction |
| ----- | --------- | --------- |
| `hcomp A [phi => tube, ...] base` | empty system | `base` |
| `hcomp A [phi => tube, ...] base` | top face (phi=1) in system | `tube @ 1` |
| `hcomp A [phi => tube, ...] base` | all tubes constant & coherent with base | `base` |
| `comp A [phi => tube, ...] base` | empty system | `base` |
| `comp A [phi => tube, ...] base` | top face (phi=1) in system | `tube @ 1` |
| `comp A [phi => tube, ...] base` | all tubes constant & coherent with base | `base` |
| `fill A [phi => tube, ...] base @ i0` | always | `base` |
| `fill A [phi => tube, ...] base @ i1` | always | `comp A [phi => tube, ...] base` |
| `fill A [phi => tube, ...] base` | empty system | `fun j -> base` |
| `fill A [phi => tube, ...] base` | top face (phi=1) in system | `tube` |
| `fill A [phi => tube, ...] base` | all tubes constant & coherent with base | `fun j -> base` |
| `hfill A [phi => tube, ...] base @ i0` | always | `base` |
| `hfill A [phi => tube, ...] base @ i1` | always | `hcomp A [phi => tube, ...] base` |
| `hfill A [phi => tube, ...] base` | empty system | `fun j -> base` |
| `hfill A [phi => tube, ...] base` | top face (phi=1) in system | `tube` |
| `hfill A [phi => tube, ...] base` | all tubes constant & coherent with base | `fun j -> base` |

**Constant-tube shortcut**: A system is *constant and coherent* when every
tube satisfies `tube @ i0 ≡ tube @ i1` and `tube @ i0 ≡ base` (i.e., the
tube is a constant path that agrees with the base). In this case, no
computation is needed — the result is simply `base` (for `hcomp`/`comp`) or
the constant path `fun j -> base` (for `fill`/`hfill`).

This optimization applies before type decomposition and is essential for
correct behavior of papp-through-VHComp reductions at interval endpoints.

### HIT Computation Rules (Data Type Decomposition)

hcomp/comp decompose through data type constructors when the tube system is
compatible (every tube produces the same constructor as the base).
fill/hfill decompose through Pi, Sigma, and data types.

#### Data Type Decomposition (hcomp/comp/fill/hfill)

| Form | Condition | Reduction |
| ----- | --------- | --------- |
| `hcomp D [phi => tube, ...] (C args)` | all tubes = `C(tube_args)` | `C(hcomp A₁ [phi => tube₁, ...] args₁, ...)` |
| `comp D [phi => tube, ...] (C args)` | all tubes = `C(tube_args)` | `C(comp A₁ [phi => tube₁, ...] args₁, ...)` |
| `fill D [phi => tube, ...] (C args)` | all tubes = `C(tube_args)` | `VPLam(j, C(fill A₁ [phi => tube₁, ...] args₁ @ j, ...))` |
| `hfill D [phi => tube, ...] (C args)` | all tubes = `C(tube_args)` | `VPLam(j, C(hfill A₁ [phi => tube₁, ...] args₁ @ j, ...))` |

Each constructor argument is composed/filled independently. For fill/hfill,
the result is a path (PLam) wrapping constructor arguments filled at the
interval variable.

#### Pi Type Decomposition (fill/hfill)

fill/hfill decompose through Pi types by introducing a lambda that applies
inner fills at the argument:

| Form | Reduction |
| ----- | --------- |
| `fill (Pi x:A. B) [phi => tube, ...] base` | `VPLam(j, VLam(x, fill B [phi => tube@x, ...] (base x) @ j))` |
| `hfill (Pi x:A. B) [phi => tube, ...] base` | `VPLam(j, VLam(x, hfill B [phi => tube@x, ...] (base x) @ j))` |

The result is a path from `base` to the composed function, where each
argument position is filled independently.

#### Sigma Type Decomposition (fill/hfill)

fill/hfill decompose through Sigma types by filling each component:

| Form | Reduction |
| ----- | --------- |
| `fill (A * B) [phi => tube, ...] base` | `VPLam(j, (fill A [phi => fst(tube), ...] (fst base) @ j, fill B [phi => snd(tube), ...] (snd base) @ j))` |
| `hfill (A * B) [phi => tube, ...] base` | `VPLam(j, (hfill A [phi => fst(tube), ...] (fst base) @ j, hfill B [phi => snd(tube), ...] (snd base) @ j))` |

Each component is filled independently and the results are paired.

This decomposes the Kan operation through each constructor argument
independently, transporting each argument through its type.

### Nat Display

Natural number values (`TCon("Nat", "suc", [TCon("Nat", "suc", [...])])`)
are displayed as their integer representation for readability:

```
suc (suc (suc zero))   displays as   3
```

---

## 15. Complete Grammar

Here is a BNF-style grammar for the Owl surface syntax. The parser is a
recursive-descent parser; precedence is encoded in the call hierarchy.

```
<file>        ::= <decl>*
<decl>        ::= "import" STRING
                | "inductive" NAME [<params>] [":" UNIV] "where" <con_list>
                  ["with" "inductive" NAME [<params>] [":" UNIV] "where" <con_list>]*
                | "inductive" NAME [<params>] [":" UNIV] "where" <con_list>
                  "with" NAME ":" <term> ":=" <term>
                | "record" NAME [<params>] "where" <field_list>
                | "def" NAME ":" <term> ":=" <term>

<params>      ::= ("(" NAME ":" <term> ")")*
<con_list>    ::= <con> ("|" <con>)*
<con>         ::= NAME ":" <con_type> ["[" <face> "," <face> "]"]
                | NAME ":" <con_type> "[[" <face> "," <face> "," <face> "," <face> "]]"
                | NAME ":" <con_type> "["+ <face> ("," <face>)* "]" "+"
                | NAME ":" <con_type>  -- ordinary (point) constructor
<con_type>    ::= <atom> ("->" <atom>)*
<field_list>  ::= <field> (";" <field>)*
<field>       ::= "field" NAME ":" <term>
<UNIV>        ::= "U0" | "U1" | "U2" | ...

<term>        ::= <lambda>
<lambda>      ::= "let" NAME [":" <term>] ":=" <term> "in" <term>
                | "by" <tactic> (";" <tactic>)*
                | "fun" <lam_binders> "=>" <term>
                | "<" NAME ">" <term>            -- path lambda
                | "forall" "(" NAME ":" <term> ")" "," <term>
                | "∀" "(" NAME ":" <term> ")" "," <term>
                | "Σ" "(" NAME ":" <term> ")" "," <term>
                | <pair>

<pair>        ::= <arrow> ("," <term>)?            -- pair or comma
<arrow>       ::= <sigma> ("->" <term>)?
<sigma>       ::= <join> ("*" <join>)*             -- right-associative
<join>        ::= <meet> ("\/" <meet>)*
<meet>        ::= <tilde> ("/\ " <tilde>)*
<tilde>       ::= "~" <tilde> | <papp>
<papp>        ::= <app> ("@" <tilde>)*             -- path application
<app>         ::= <prefix_or_atom>+ <record_update>?
<record_update> ::= "{" NAME "=" <term> ("," NAME "=" <term>)* "}"

<prefix_or_atom>
              ::= "fst" <prefix_or_atom>           -- first projection
                | "snd" <prefix_or_atom>           -- second projection
                | "ua" <prefix_or_atom>            -- univalence
                | "transport" <prefix_or_atom> <prefix_or_atom>
                | "equivFwd" <prefix_or_atom> <prefix_or_atom>
                | "lift" <prefix_or_atom>          -- lift into higher universe
                | "lower" <prefix_or_atom>         -- lower from higher universe
                | <atom>

<atom>        ::= NAME                             -- variable, constructor, i0, i1
                | INT                              -- 0 = i0, 1 = i1, other = error
                | "(" <term> ")"                   -- parenthesized
                | "Path" <prefix_or_atom> <prefix_or_atom> <prefix_or_atom>
                | "PathP" <prefix_or_atom> <prefix_or_atom> <prefix_or_atom>
                | "hcomp" <prefix_or_atom> (<system> | <prefix_or_atom> <prefix_or_atom>) <prefix_or_atom>
                | "comp" <prefix_or_atom> (<system> | <prefix_or_atom> <prefix_or_atom>) <prefix_or_atom>
                | "fill" <prefix_or_atom> (<system> | <prefix_or_atom> <prefix_or_atom>) <prefix_or_atom>
                | "hfill" <prefix_or_atom> (<system> | <prefix_or_atom> <prefix_or_atom>) <prefix_or_atom>
                | "Equiv" <prefix_or_atom> <prefix_or_atom>
                | "mkEquiv" <prefix_or_atom> <prefix_or_atom> <prefix_or_atom> <prefix_or_atom> <prefix_or_atom> <prefix_or_atom>
                | "Glue" <prefix_or_atom> <prefix_or_atom> <prefix_or_atom>
                | "Partial" <prefix_or_atom> <prefix_or_atom>
                | "glue" <prefix_or_atom> <prefix_or_atom> <prefix_or_atom>
                | "unglue" <prefix_or_atom> <prefix_or_atom> <prefix_or_atom>
                | "[" "_" "|" <join> "]" <prefix_or_atom>   -- partial element type (bracket)
                | "Prop"                      -- proposition universe (U0)
                | "SSet"                       -- strict set universe (U1)
                | <match>

<system>      ::= "[" <system_entry> ("," <system_entry>)* "]"
<system_entry>::= <join> "=>" <term>

<match>       ::= "match" NAME "return" <term> "with" <cases>
                | "match" <term> "return" <term> "with" <cases>
<cases>       ::= (<case>)+
<case>        ::= "|" <pattern> ("|" <pattern>)* "=>" <term>
<pattern>     ::= NAME <binders> ["as" NAME]
                | NAME "{" <field_pats> "}" ["as" NAME]
                | NAME
<field_pats>  ::= NAME "=" <binders> ("," NAME "=" <binders>)*
<binders>     ::= NAME* | "_"

<lam_binders> ::= NAME+ | ("(" NAME+ ":" <term> ")")+

<tactic>      ::= "exact" <term>
                | "intro" NAME+
                | "apply" <term>
                | "assumption"
                | "reflexivity"
                | "symmetry"
                | "split"
                | "constructor" NAME?
                | "destruct" NAME
                | "transitivity"
                | "compute"
                | "trivial"

<face>        ::= <face_atom> ("\/" <face_atom>)*
<face_atom>   ::= <face_lit> ("/\ " <face_lit>)*
<face_lit>    ::= "~" <name> | <name>
```

### Notes on the Grammar

**Interval variables**: Any identifier can serve as an interval variable when
bound by path lambda (`<i> ...`). The parser tracks bound interval variables
separately from term variables. The special names `i0` and `i1` are always
resolved as interval endpoints, not as regular variables.

**Integer literals**: The integers `0` and `1` are parsed as interval endpoints
(`i0` and `i1`). Other integers are not valid in the surface syntax.

**Match scrutinee**: The `match` form accepts either a bare name (resolved
from scope) or an arbitrary term as the scrutinee.

**System syntax**: hcomp, comp, fill, and hfill accept either a
multi-face system `[phi1 => tube1, phi2 => tube2]` or a legacy
single-face form `phi tube`.

**System types**: `[phi => A, psi => B]` can be used as a type (not just
in Kan operations). System types represent partial functions and must be
coherent — overlapping faces must agree on their types.

---

## 16. Worked Examples

### Example 1: Identity Function

```
def id : ∀ (A : U0), A -> A := fun A x => x
```

### Example 2: Natural Numbers and Addition

```
inductive Nat where
  | zero : Nat
  | suc : Nat -> Nat

def add : Nat -> Nat -> Nat := fun m n =>
  match m return Nat with
  | zero => n
  | suc m' => suc (add m' n)

def four : Nat := add (suc (suc zero)) (suc (suc zero))
-- Evaluates to: 4
```

### Example 3: Higher Inductive Type (Circle)

```
inductive S1 where
  | base : S1
  | loop : S1 [ base , base ]
```

Here `loop` is a path constructor with:
- No ordinary arguments
- `face0 = base` (loop at i0 is base)
- `face1 = base` (loop at i1 is base)

### Example 4: Parameterized Truncation

```
inductive Trunc (A : U0) where
  | inc : A -> Trunc A
  | trunc : A -> A -> Trunc A [ inc trunc_0 , inc trunc_1 ]
```

The eliminator for `Trunc` proves a property by handling:
1. The `inc` case: prove `P (inc a)` for an arbitrary `a : A`
2. The `trunc` case: prove `Path (P (trunc a b))` for arbitrary `a, b`

```
def trunc_ind :
  forall (A : U0) (P : Trunc A -> U0),
  (forall (a : A), P (inc a)) ->
  forall (x : Trunc A), P x :=
  fun A P h x =>
    match x return P x with
    | trunc a b i => <j> h a
    | inc a => h a
```

### Example 5: Parameterized Pushout

```
inductive Pushout (A : U0) (B : U0) (C : U0) where
  | left : A -> Pushout A B C
  | right : B -> Pushout A B C
  | glue : C -> Pushout A B C [ left glue_0 , right glue_0 ]
```

The eliminator handles three cases:
1. `left a`: prove `P (left a)` for arbitrary `a : A`
2. `right b`: prove `P (right b)` for arbitrary `b : B`
3. `glue c`: prove `Path (P (glue c))` connecting the `left` and `right` cases

```
def pushout_elim :
  forall (A B C : U0) (P : Pushout A B C -> U0),
  (forall (a : A), P (left a)) ->
  (forall (b : B), P (right b)) ->
  (forall (c : C), Path (P (glue c))) ->
  forall (x : Pushout A B C), P x :=
  fun A B C P f g h x =>
    match x return P x with
    | glue c i => <j> f c
    | left a => f a
    | right b => g b
```

### Example 6: Transport over Univalence

```
def transportExample :
  forall (A : U0), forall (B : U0), Equiv A B -> A -> B :=
  fun A B e a => transport (<i> ua e @ i) a
```

This constructs a function that converts `A` to `B` given an equivalence,
using transport along the univalence path.

### Example 7: Kan Operations (comp, fill, hfill)

```
-- Heterogeneous composition: composes a family of paths
def comp_example : Nat :=
  comp Nat 1 (<i> suc zero) (suc zero)

-- Dependent fill: constructs a path from base to comp
def fill_example : Nat :=
  fill Nat 1 (<i> suc zero) (suc zero) @ i1

-- Homogeneous fill: constructs a path from base to hcomp
def hfill_example : Nat :=
  hfill Nat 1 (<i> suc zero) (suc zero) @ i1

-- Fill in a function: variable tube
def fill_fn : Nat -> Nat :=
  fun n => fill Nat 1 (<i> n) n @ i1

-- Transport over comp
def transport_comp : Nat :=
  transport (<i> Nat)
    (comp Nat 1 (<i> suc zero) (suc (suc zero)))
```

### Example 8: Tactic Proofs

```
def id : ∀ (A : U0), A -> A := by intro A x; exact x

def const_zero : Nat := by exact zero

def id_nat : Nat -> Nat := by intro x; assumption

def id_nat_fn : Nat -> Nat := fun x => x

def id_nat_apply : Nat -> Nat := by intro x; apply id_nat_fn; exact x

def add_one : Nat -> Nat := fun n => suc n

def double_apply : Nat -> Nat := by intro x; apply add_one; apply add_one; exact x

def refl_path : Path Nat zero zero := by reflexivity

def sym_path : Path Nat zero zero := by symmetry; reflexivity

def pair_val : Nat * Nat := by split; exact (suc zero); exact (suc (suc zero))

def mk_two : Nat := by constructor suc; exact (suc zero)

def trivial_refl : Path Nat zero zero := by trivial

inductive Bool where
  | true : Bool
  | false : Bool

def neg : Bool -> Bool :=
  by intro b; destruct b; exact false; exact true
```

### Example 9: Torus with Square Constructor

```
inductive Torus where
  | base : Torus
  | line1 : Torus [ base , base ]
  | line2 : Torus [ base , base ]
  | square : Torus [[ base , base , line2 , line2 ]]

-- Identity function on Torus
def id_torus : Torus -> Torus :=
  fun x => match x return Torus with
  | base => base
  | line1 i => <j> line1 @ j
  | line2 j => <k> line2 @ k
  | square r s => <i> <j> square @ i @ j
```

The square case body `<i> <j> square @ i @ j` constructs a surface by
applying the square constructor at the two fresh interval variables. The
type checker verifies this matches the expected nested PathP type:

```
PathP (<r> PathP (<s> Torus) base base) line2 line2
```

### Example 10: Mutual Dependencies via Match

```
inductive Nat where
  | zero : Nat
  | suc : Nat -> Nat

def isZero : Nat -> Bool :=
  fun n => match n return Bool with
  | zero => true
  | suc _ => false
```

### Example 11: Partial Elements

```
-- Partial elements restrict a type to a face
def partial_nat : [_ | i1] Nat := suc zero

-- Partial elements are used in Glue type construction
-- and cubical subtyping
```

### Example 12: Prop and SSet Universes

```
-- Prop is impredicative: Pi over Prop stays in Prop
def trivial_prop : Prop := Prop

-- SSet lives at level 1
def strict_set_type : SSet := SSet
```

### Example 13: Universe Lifting

```
inductive Nat where
  | zero : Nat
  | suc : Nat -> Nat

-- Lift a Nat into a higher universe
def lifted_zero : lift Nat := lift zero
```

### Example 14: Mutual Inductive Types

```
inductive even where
  | even_zero : even
  | even_suc : even -> even
with inductive odd where
  | odd_one : odd
  | odd_suc : odd -> odd
```

Both types are visible to each other's constructors. The second type can
reference constructors of the first (forward reference).

### Example 15: Induction-Recursion

```
inductive Nat where
  | zero : Nat
  | suc : Nat -> Nat
with isZero : Nat -> Nat :=
  fun n => match n return Nat with
  | zero => suc zero
  | suc _ => zero
```

The function `isZero` is defined simultaneously with `Nat` and can
pattern-match on `Nat` values.

### Example 16: Structural Recursion Guard

```
inductive Nat where
  | zero : Nat
  | suc : Nat -> Nat

def add : Nat -> Nat -> Nat := fun m n =>
  match m return Nat with
  | zero => n
  | suc m' => suc (add m' n)
-- add recurses on m', which is a strict subterm of m: OK
```

### Example 17: Record Types

```
record Point where
  field x : Nat
  field y : Nat

-- Construction via auto-generated constructor mkPoint
def origin : Point := mkPoint zero zero

-- Field projection via dot notation
def get_x : Point -> Nat := fun p => p.x
def get_y : Point -> Nat := fun p => p.y

-- Parameterized record
record Pair (A : Type) (B : Type) where
  field fst : A
  field snd : B

def swap : forall (A : Type) (B : Type), Pair A B -> Pair B A :=
  fun A B p => mkPair p.snd p.fst
```

### Example 18: Cubical Stress Test (Section 5 Features)

```
inductive Nat where
  | zero : Nat
  | suc : Nat -> Nat

-- Face lattice: negation, meet, join
def face_example : Nat :=
  hcomp Nat [~i0 /\ i1 => <i> suc zero] zero

-- Multi-face Kan operations
def multi_hcomp : Nat :=
  hcomp Nat [i0 => <i> zero, i1 => <i> suc zero] (suc zero)

-- Constant-tube shortcut (all tubes coherent with base → base)
def const_hcomp : Nat :=
  hcomp Nat [i1 => <i> suc zero] (suc zero)

-- Transport through Pi type
def transport_pi : Nat :=
  (transport (<i> Nat -> Nat) (fun x => suc x)) zero
```

---

## 17. Error Types

The typechecker produces the following error categories:

| Error | Meaning |
| ----- | ------- |
| `UnboundVariable(x)` | Variable `x` is not in scope |
| `TypeMismatch(expected, got)` | Inferred type does not match expected type |
| `ExpectedPi(ty)` | Expected a function type, got `ty` |
| `ExpectedPath(ty)` | Expected a path type, got `ty` |
| `ExpectedSigma(ty)` | Expected a pair type, got `ty` |
| `ExpectedEquiv(ty)` | Expected an equivalence type, got `ty` |
| `ExpectedUniverse(ty)` | Expected a universe type, got `ty` |
| `NotAnInterval(t)` | Expected an interval expression, got `t` |
| `CannotInfer(ty)` | Cannot infer type of `ty` without annotation |
| `Other(msg)` | Other error message |
| `UnknownDatatype(d)` | Unknown datatype name `d` |
| `UnknownConstructor(d, c)` | Constructor `c` not found in datatype `d` |
| `WrongNumberOfArgs{..}` | Constructor got wrong number of arguments |
| `BadElimCase{..}` | Eliminator case has invalid boundary conditions |
| `MissingCase(c)` | Eliminator is missing a case for constructor `c` |
| `ExpectedData(ty)` | Expected a datatype, got `ty` |
| `PathPNotTypeFamily(ty)` | First argument of PathP must be a type family |
| `TerminationViolation{..}` | Recursive call does not pass a subterm of the scrutinee |
| `EtaFuelExhausted(..)` | Eta-equality check ran out of fuel |

Additionally, a separate positivity check runs during datatype declaration:

| Error | Meaning |
| ----- | ------- |
| `PositivityError` | Datatype appears in non-positive position in a constructor |

### Debug Output

When the `--debug` or `-d` flag is used, errors include additional context:

- **Definition context**: Errors show which definition failed (e.g., "in definition 'myFunc':")
- **Debug scope**: The typechecker logs the term being checked, the expected type, and the context depth
- **NbE trace**: All normalization-by-evaluation reduction steps are printed on both success and error

---

## 18. Running Owl

### Check Mode

Type-check a file without evaluating:

```
owl check file.owl
```

### Run Mode

Type-check and evaluate `main` (or last definition):

```
owl run file.owl
```

### Example

```
$ owl run examples/nat.owl
main : Nat = 4
```
