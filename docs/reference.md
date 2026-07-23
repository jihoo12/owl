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
| `with`        | Separator before match cases               |
| `Type`        | Alias for universe `U0`                    |
| `Path`        | Path type former                           |
| `PathP`       | Dependent path type (type family required) |
| `hcomp`       | Homogeneous composition                    |
| `comp`        | Heterogeneous composition                  |
| `fill`        | Dependent fill (heterogeneous)             |
| `hfill`       | Homogeneous fill                           |
| `Equiv`       | Equivalence type                           |
| `mkEquiv`     | Construct an equivalence                   |
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

### Symbols and Operators

| Symbol    | Meaning                            | Associativity |
| --------- | ---------------------------------- | ------------- |
| `->`      | Non-dependent function type        | right         |
| `=>`      | Lambda arrow                       | --            |
| `:=`      | Definition body separator          | --            |
| `*` / `x` | Non-dependent product (Sigma) type | right         |
| `@`       | Path application                   | left          |
| `/\`      | Interval meet (conjunction)        | right         |
| `\/`      | Interval join (disjunction)        | right         |
| `~`       | Interval negation                  | prefix        |
| `<i>`     | Path lambda (binds interval var)   | --            |
| `,`       | Pair separator / tactic separator  | --            |
| `:`       | Type annotation                    | --            |
| `;`       | Tactic separator                   | --            |
| `\|`      | Match case separator               | --            |

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
```

Universes are stratified to avoid paradoxes. Each universe contains the types
of the previous level:

```
U0 : U1 : U2 : ...
```

**Cumulativity**: if `n <= m`, then `U_n` is a subtype of `U_m`.

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
  | trunc_id : forall (a b : Trunc A), Path (Trunc A) a b
```

`trunc_id` is a path constructor: it takes two points and produces a path
between them, asserting that all points in `Trunc A` are equal.

#### Example: Pushout (Double Pushout)

```
inductive Pushout (A : U0) (B : U0) (C : U0) where
  | left : A -> Pushout A B C
  | right : B -> Pushout A B C
  | glue : forall (c : C), Path (Pushout A B C) (left c) (right c)
```

`glue` is a path constructor connecting `left c` to `right c` for each
`c : C`.

#### Example: Suspension

```
inductive Susp (A : U0) where
  | north : Susp A
  | south : Susp A
  | merid : forall (a : A), Path (Susp A) north south
```

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

### Elimination Semantics

The match expression is desugared to the core eliminator form:

```
elim[M] { case1 | case2 | ... } scrutinee
```

where `M` is the motive function. Reduction occurs when the scrutinee is a
constructor value: the matching case body is selected and its binders are
substituted with the constructor's arguments.

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

### Kan Operation Reductions

| Form | Condition | Reduction |
| ----- | --------- | --------- |
| `comp A phi tube base` | `phi = 1` | `tube @ 1` |
| `comp A phi tube base` | `phi = 0` | `base` |
| `fill A phi tube base @ i0` | always | `base` |
| `fill A phi tube base @ i1` | always | `comp A phi tube base` |
| `fill A phi tube base` | `phi = 1` | `tube` |
| `fill A phi tube base` | `phi = 0` | `fun j -> base` |
| `hfill A phi tube base @ i0` | always | `base` |
| `hfill A phi tube base @ i1` | always | `hcomp A phi tube base` |
| `hfill A phi tube base` | `phi = 1` | `tube` |
| `hfill A phi tube base` | `phi = 0` | `fun j -> base` |

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
                | "def" NAME ":" <term> ":=" <term>

<params>      ::= ("(" NAME ":" <term> ")")*
<con_list>    ::= <con> ("|" <con>)*
<con>         ::= NAME ":" <con_type> ["[" <face> "," <face> "]"]
<con_type>    ::= <atom> ("->" <atom>)*
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
<app>         ::= <prefix_or_atom>+

<prefix_or_atom>
              ::= "fst" <prefix_or_atom>           -- first projection
                | "snd" <prefix_or_atom>           -- second projection
                | "ua" <prefix_or_atom>            -- univalence
                | "transport" <prefix_or_atom> <prefix_or_atom>
                | "equivFwd" <prefix_or_atom> <prefix_or_atom>
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
                | "glue" <prefix_or_atom> <prefix_or_atom> <prefix_or_atom>
                | "unglue" <prefix_or_atom> <prefix_or_atom> <prefix_or_atom>
                | <match>

<system>      ::= "[" <system_entry> ("," <system_entry>)* "]"
<system_entry>::= <join> "=>" <term>

<match>       ::= "match" NAME "return" <term> "with" <cases>
                | "match" <term> "return" <term> "with" <cases>
<cases>       ::= ("|" NAME <binders> "=>" <term>)+
<binders>     ::= NAME*

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
  | trunc_id : forall (a b : Trunc A), Path (Trunc A) a b
```

The eliminator for `Trunc` proves a property by handling:
1. The `inc` case: prove `P (inc a)` for an arbitrary `a : A`
2. The `trunc_id` case: prove `Path (P (trunc_id a b))` for arbitrary `a, b`

```
def trunc_ind :
  forall (A : U0) (P : Trunc A -> U0),
  (forall (a : A), P (inc a)) ->
  forall (x : Trunc A), P x :=
  fun A P h x =>
    match x return P x with
    | trunc_id a b => <i> h a
    | inc a => h a
```

### Example 5: Parameterized Pushout

```
inductive Pushout (A : U0) (B : U0) (C : U0) where
  | left : A -> Pushout A B C
  | right : B -> Pushout A B C
  | glue : forall (c : C), Path (Pushout A B C) (left c) (right c)
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
    | glue c => <i> f c
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

### Example 9: Mutual Dependencies via Match

```
inductive Nat where
  | zero : Nat
  | suc : Nat -> Nat

def isZero : Nat -> Bool :=
  fun n => match n return Bool with
  | zero => true
  | suc _ => false
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
| `EtaFuelExhausted(..)` | Eta-equality check ran out of fuel |

Additionally, a separate positivity check runs during datatype declaration:

| Error | Meaning |
| ----- | ------- |
| `PositivityError` | Datatype appears in non-positive position in a constructor |

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
