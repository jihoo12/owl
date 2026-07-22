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
| `match`       | Pattern matching / elimination             |
| `return`      | Annotate match return type                 |
| `with`        | Separator before match cases               |
| `Type`        | Alias for universe `U0`                    |
| `Path`        | Path type former                           |
| `hcomp`       | Homogeneous composition                    |
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
| `in`    | Interval variable n (de Bruijn) |

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
Sigma (x : A), B         -- dependent
A * B                    -- non-dependent (shorthand)
```

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

Constructors may take arguments of any type:

```
inductive List (A : U0) where
  | nil : List A
  | cons : A -> List A -> List A
```

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

---

## 7. Pattern Matching and Elimination

### Syntax

```
match scrutinee return ReturnType with
  | con1 => body1
  | con2 arg1 arg2 => body2
  | con3 arg1 arg2 arg3 => body3
```

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

### Interval Algebra

Interval expressions support:

| Operation | Syntax | Meaning |
| --------- | ------ | ------- |
| Left endpoint | `i0` | 0 |
| Right endpoint | `i1` | 1 |
| Variable | `in` | Interval variable at de Bruijn index n |
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
hcomp A phi tube base
```

Homogeneous composition composes paths along a face `phi`:

- `A` : the type
- `phi` : a face formula (cube/DNF)
- `tube : I -> A` a function providing paths along each face
- `base : A` the base element

### Boundary Reductions

```
hcomp A phi tube base @ i0  =  base
hcomp A phi tube base @ i1  =  tube @ i1
```

The tube must satisfy `tube @ 0 = base` on every face of `phi`.

---

## 10. Glue Types and Univalence

### Glue Types

```
Glue A [phi] (te)
```

Glue type construction: `A` is the base type, `phi` is a face restriction,
and `te` provides equivalences on the face where `phi` is true.

When `phi` is false, `Glue A [phi] (te)` reduces to `A`.
When `phi` is true, it reduces to the domain of the equivalence.

### Glue Element Introduction

```
glue [phi] t a
```

Constructs a value of Glue type from:
- `t` : the cap (in the equivalence domain, when `phi` is true)
- `a` : the base (in `A`)

### Glue Element Elimination

```
unglue [phi] te g
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

## 11. Tactic Mode

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

## 12. Imports and Modules

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

## 13. Evaluation and Normalization

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

### Nat Display

Natural number values (`TCon("Nat", "suc", [TCon("Nat", "suc", [...])])`)
are displayed as their integer representation for readability:

```
suc (suc (suc zero))   displays as   3
```

---

## 14. Complete Grammar

Here is a simplified BNF-style grammar for the Owl surface syntax:

```
<file>       ::= <decl>*
<decl>       ::= "import" STRING
               | "inductive" NAME [":" ULEVEL] "where" <con_list>
               | "def" NAME ":" <term> ":=" <term>

<con_list>   ::= <con> ("|" <con>)*
<con>        ::= NAME [":" <con_type>] ["[" <face> "," <face> "]"]
<con_type>   ::= <type_atom> ("->" <type_atom>)*

<term>       ::= "let" NAME [":" <term>] ":=" <term> "in" <term>
               | "by" <tactic> (";" <tactic>)*
               | "fun" <binders> "=>" <term>
               | "<" NAME ">" <term>
               | "forall" "(" NAME ":" <term> ")" "," <term>
               | "Sigma" "(" NAME ":" <term> ")" "," <term>
               | <pair_term>

<pair_term>  ::= <arrow> ("," <term>)?
<arrow>      ::= <sigma> ("->" <term>)?
<sigma>      ::= <app> ("*" <app>)?
<app>        ::= <app> <atom> | <atom>
<atom>       ::= NAME | INT | "(" <term> ")"
               | <term> "@" <atom>
               | "fst" <atom> | "snd" <atom>
               | "match" <term> "return" <term> "with" <cases>
               | "hcomp" <atom> <atom> <atom> <atom>
               | "Equiv" <atom> <atom>
               | "mkEquiv" <atom> <atom> <atom> <atom> <atom> <atom>
               | "equivFwd" <atom> <atom>
               | "ua" <atom>
               | "transport" <atom> <atom>
               | "Glue" <atom> "[" <face> "]" "(" <atom> ")"
               | "glue" "[" <face> "]" <atom> <atom>
               | "unglue" "[" <face> "]" <atom> <atom>

<cases>      ::= ("|" NAME <binders> "=>" <term>)*
<binders>    ::= NAME*
<tactic>     ::= "exact" <term>
               | "intro" NAME+
               | "apply" <term>
               | "assumption"
               | "reflexivity"
               | "symmetry"
               | "split"

<face>       ::= <face_atom> ("\/" <face_atom>)*
<face_atom>  ::= <face_lit> ("/\ " <face_lit>)*
<face_lit>   ::= "i" INT | "~" "i" INT
```

---

## 15. Worked Examples

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

### Example 4: Transport over Univalence

```
def transportExample :
  forall (A : U0), forall (B : U0), Equiv A B -> A -> B :=
  fun A B e a => transport (<i> ua e @ i) a
```

This constructs a function that converts `A` to `B` given an equivalence,
using transport along the univalence path.

### Example 5: Tactic Proofs

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
```

### Example 6: Mutual Dependencies via Match

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

## 16. Error Types

The typechecker produces the following error categories:

| Error | Meaning |
| ----- | ------- |
| `UnboundVariable(x)` | Variable `x` is not in scope |
| `TypeMismatch(expected, got)` | Inferred type does not match expected type |
| `ExpectedPi(ty)` | Expected a function type, got `ty` |
| `ExpectedPath(ty)` | Expected a path type, got `ty` |
| `ExpectedSigma(ty)` | Expected a pair type, got `ty` |
| `ExpectedUniverse(ty)` | Expected a universe type, got `ty` |
| `CannotInfer(ty)` | Cannot infer type of `ty` without annotation |
| `UnknownDatatype(d)` | Unknown datatype name `d` |
| `UnknownConstructor(d, c)` | Constructor `c` not found in datatype `d` |
| `WrongNumberOfArgs{..}` | Constructor got wrong number of arguments |
| `MissingCase(c)` | Eliminator is missing a case for constructor `c` |
| `PositivityError{..}` | Datatype appears in negative position |
| `EtaFuelExhausted(..)` | Eta-equality check ran out of fuel |

---

## 17. Running Owl

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
