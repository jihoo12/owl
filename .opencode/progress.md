# Summary

## Goal
Implement Section 6.1 (Normalization) and Section 6.2 (Type Checking) from TODO.md: nbe_eval memoization, `_` holes with pattern unification.

## Status: MAIN IMPLEMENTATION DONE

### Completed
- **nbe_eval memoization**: `NBE_EVAL_CACHE` thread-local `HashMap<Term, Term>` in `nbe/mod.rs`. Cache hit/miss in `nbe_eval`. `clear_nbe_cache()`.
- **Metavar store**: `METAVAR_SOLUTIONS` thread-local `Vec<Option<Term>>` with helpers: `fresh_meta_id()`, `solve_meta()`, `get_meta_solution()`, `clear_metavars()`, `meta_mentions()` (occurs check), `try_solve_meta()`, `zonk()` (replace solved metas), `has_meta_in_term()`, `term_children_ref()`.
- **Parser** (`grammar.rs`): `_` in `parse_atom` → `Term::Meta(fresh_meta_id())`.
- **Typechecker** (`mod.rs`): `Meta` in `type_level_dt` returns `Ok(0)`. `Meta` in `check_dt` delegates to equality. `infer_dt` errors with "cannot infer type of `_`".
- **Equality checker** (`equality.rs`): Pattern unification in `eta_eq_uncached` — `Meta(i) = rhs` or `lhs = Meta(i)` tries `try_solve_meta` with occurs check.
- **Cache coherency**: Don't cache nbe_eval results containing Meta. `clear_nbe_cache()` called between top-level definitions (not metavar store).
- **Driver** (`driver.rs`): Skip universe-level check for Meta type annotations. `zonk` in `process_def` and `normalize_definition`. NBE cache cleared between definitions; metavar solutions persist through `normalize_definition`.

### Verified
- `def foo : _ := zero` → `foo : Nat = 0` (type hole solved by pattern unification)
- `def foo : Nat -> _ := fun x => x` → `foo : forall (_ : Nat), Nat = fun x => x` (hole in Pi codomain)
- `def foo : _ := 0` with interval `0` typechecks
- All 138 existing tests pass

### Not Yet Done
- **Value interning (Rc wrapping)** — medium priority, future work
- **Expected-type propagation in typechecker** — medium priority, future work
