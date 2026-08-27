# TODO.md — Remaining improvements for owl

> The checklist below is the live status tracker (`[x]` = done, `[ ]` = open).

## Completed (implementation log)

- [x] **H4 — Implicit arguments + global instance search.** Added implicit binder syntax `{x : A}` (Lean-style) with `TPi` flag. Parser recognizes `{name : type}` in term position (both top-level and in `->` codomains). Pretty-printer shows implicit binders as `{x : A} -> B`. Typechecker auto-fills implicit arguments during `TApp` by searching the context for a term whose type definitionally matches the implicit binder's domain — enables `def f : {C : CommRing A ...}, ... := ...` without threading `C` explicitly at call sites. Global `Env.instances` database tracks `CommRing`/`Field`/`Group`/`Module` instances at definition time; `find_implicit_arg` searches local context first, then falls back to global instance DB (currently context-only since instances are registered in defs). Updated `ring`/`field`/`group` tactics to resolve instances from global env via context. Full suite **233 green**; verification pipeline OK.
  Motivated by H4 goal: "without typeclasses, every theorem must thread `CommRing R` explicitly". Implicit binders let users write `def add_comm : {C : CommRing A ...}, forall x y, add x y = add y x := ...` and call it as `add_comm x y` with `C` inferred from context (or global instance DB). Remaining: implicit lambda syntax `fun {x} => ...` for constructing implicit functions; instance DB search for imported instances not yet in local context.

- [x] **Performance pass — `cargo test` 102.8 s → ~31–54 s, tactic proofs verified once, CLI stack-safe.**
  Motivated by H5 iteration pain (long test runs + debug-build stack overflows). Profiled
  first with throwaway chokepoint timers + an allocation-counting global allocator
  (`field_demo.owl`: 53.9 s release, 2.0 G allocations / 157 GiB churn; ~50 % of wall time
  was the solvers' *internal* `check_dt` duplicating the driver's mandatory re-check, and
  NbE internals — normalize/quote/shift/subst/eta_eq — were only ~4 s, so the cost is
  per-node Term cloning inside one infer/check traversal, not arithmetic). Three changes:
  (1) **verify-once policy** — ring/field/group's internal kernel checks are now
  `--debug`-only diagnostics; production runs rely on the single mandatory
  `process_def` re-check (soundness unchanged), and on rejection of a tactic-generated
  body the driver appends a "re-run with --debug" hint (`examples/field_demo.owl`
  53.9 → 27.8 s from this alone). omega's `check_dt` candidate filter is load-bearing
  and untouched. (2) **opt-level 2 for dev/test profiles** (debug assertions kept) —
  debug CLI ≈ release now; incremental builds 2.5 → 5.5 s. (3) **256 MiB-stack worker
  thread** wrapping all `owl` CLI commands in `src/main.rs` (lazily committed; verified
  under `ulimit -s 1024` on stress_hit_elimination). Also added a permanent
  `OWL_TIMINGS=1` phase timer to stderr (tactic-resolve / kernel-recheck / output-norm),
  updated verify.sh (--quick skip list obsolete), AGENTS.md §4/§6/§8, and removed all
  profiling scaffolding. Verified: full suite **233 green** (~31 s warm); field_demo
  release+debug ≈ 30 s each (was 53.9 / 99.5); bad_examples still fail;
  group_solver_rejects_non_identity etc. intact.

- [x] **H5 started — shared structure library (`lib/algebra.owl`) with the `Module` record.**
  Consolidates `CommRing`/`Group`/`Field` documentation-and-declarations in one library file
  (tactic resolution matches datatype names, so pre-existing inline declarations in
  examples/comm_ring_demo.owl and lib/field_laws.owl keep working unchanged) and introduces
  **`Module`**: an additive group `M` with scalar multiplication over a bundled ring, whose
  ring side is carried by a *record-typed parameter* `C : CommRing A add mul zero one` — the
  first use of records-as-parameters in the kernel, verified to project correctly
  (`Mod.smul_one x`, `Mod.smul_dist_r r s x` in examples/module_demo.owl). Module v1 carries
  seven laws (additive assoc/unit/inverse on M, both scalar distributivities, scalar
  associativity, unitality); additive commutativity of M is deliberately omitted as
  derivable over commutative rings. The self-module instance and concrete `IntCommRing`
  remain blocked on the int assoc/distributivity proofs deferred from H3 (case-matrix and
  required nested-induction bridges analyzed; dedicated proving session needed). Verified:
  cargo check clean; lib/algebra.owl + examples/module_demo.owl typecheck; full suite green.

- [x] **H3 — Int `by omega` + first batch of integer algebra in lib/ring_laws.owl.**
  **omega over Int** (`src/cubical/omega.rs`): the tactic's machinery (definitional
  reflexivity + lemma-instance matching with argument permutations) was already
  carrier-agnostic — only the goal check hardcoded `TData("Nat")`. It now accepts a carrier
  whitelist (`Nat`, `Int`) via `supported_carrier`, with error messages naming the carrier.
  `examples/int_demo.owl` exercises both tiers over Int: eight definitional-computation
  goals (`int_add` across sign combinations, `int_neg` double negation, `int_sub`,
  `int_mul` sign cases) plus two lemma-matching goals, and a Nat lemma-matching goal in the
  same file to prove carrier coexistence. **Int algebra** (`lib/ring_laws.owl` Part 4,
  ten new proofs): congruence glue (`int_trans/sym`, `int_cong_add_l/r`, `int_cong_neg`,
  `int_cong_mul_l/r`), `int_add_0_l/r` (the left law case-splits because the outer match is
  stuck on the neutral argument; the right law lifts `_owl_nat_add_zero_r`), `int_add_comm`
  (mixed-sign branches agree definitionally on `_owl_add_pos_neg`; same-sign lift
  `_owl_add_comm`), `int_neg_neg` (inner case-split; both branches compute), `int_mul_comm`
  (mixed-sign both reduce to the same `_owl_MPN` application), and unit/zero multiplication
  laws (`int_mul_0_l/r`, `int_mul_1_l/r` — the `1_r` negsuc branch collapses
  definitionally, an earlier draft's unnecessary inner case-split had a wrong zero-case).
  **Deferred**: `int_add_assoc`, `int_mul_assoc`, distributivity, and the full `CommRing`
  record bundling that would switch `by ring` onto Int — these are the remaining gap before
  H5 can build on a complete int-ring; noted under §H3's follow-up.
  Verified: driver test `int_omega_example_checks`; lib/ring_laws.owl, examples/int_demo.owl,
  examples/omega_demo.owl, examples/ring_demo.owl all check; full `cargo test`
  **232 green**; docs/reference.md gained an `#### omega` section.

- [x] **Section B closed — group solver (`by group with G`) and equality chaining (`by eq`).**
  **Group solver** (`src/cubical/group.rs`, ~700 lines): proves word identities over an
  abstract `Group A mul inv one` record. Both goal sides are classified into a structure
  tree (every node carries its *own source term* — an earlier draft reused child endpoints,
  which misanchored generated proofs) and reduced to signed-generator words via free
  reduction (stack cancellation of adjacent opposite letters with definitionally-equal
  atoms). Proof generation: `gen` emits right-associated-rendering proofs; products compose
  children congruences with a front-peeling `concat_pf` whose junction cancellations surface
  when the peeled prefix is a single letter (plus a trailing `mul l one → l` repair when the
  suffix reduces to empty); inversion uses `finisher_inv` — distribution swaps factors, so
  the inverted word reads *left*-associated, and `conv_lr` bridges back to canonical right-
  association by iterated associativity + a grow-from-the-back bridge. Two subtleties cost
  real debugging: (1) ring_laws/field_laws name their congruence lemmas by the *varying*
  side (`cong_mul_l : Path (a·n) (b·n)`), so the fixed-context wrappers are crossed; (2)
  `TPath`'s first field is the carrier — the trans-shape matcher originally compared it as
  an endpoint. Law set is deliberately pragmatic (mirroring Field): `inv_one`, `inv_inv`,
  and swapping `inv_mul` are primitive fields. Instance search included (`Group` record by
  carrier match); non-identities rejected with a word-mismatch error.
  **Equality chaining** (`src/cubical/eq.rs`): closes `Path A u v` goals by reflexivity,
  direct hypothesis in either orientation (backward = inline `<i> p @ ~i`), or BFS over all
  path-typed context hypotheses (endpoints matched up to normalization, monomorphic use)
  composed through a **context-provided** transitivity lemma named `_owl_trans`/`trans`,
  found by shape-matching the normalized type (`... Path x y -> Path y z -> Path x z`) with
  endpoint comparison done at a common binder depth (captures lifted out of their Pi frames).
  Hand-rolling the hcomp composition was tried and abandoned: hypothesis-path applications
  do not reduce under endpoint coherence the way lambda-bound ones do. Chaining without a
  lemma fails with guidance to import lib/ring_laws.owl.
  Verified: parser keyword/parse coverage; driver tests `group_demo_example_checks`
  (64 MiB stack), `group_solver_rejects_non_identity`, `eq_tactic_refl_sym_chain`
  (refl/direct/2-hop/3-hop), `eq_tactic_needs_trans_lemma_for_chains`;
  `examples/group_demo.owl` added to the sweep (6 identities incl. inner/mid-word
  cancellation, double-inverse, inv-distribution, unit folding); full `cargo test`
  **231 green**; docs/reference.md tactic sections updated.

- [x] **Module instantiation — `module N = M (e1) ... (en)`.** Parser (`parse_module_decl`):
  after the name, an `=` switches to the instantiation form — source module name resolved
  to its full dotted path by `resolve_module_source` (innermost-qualified candidates first,
  accepted when it prefixes known globals), then self-delimiting parenthesized arguments;
  new `Decl::ModuleInst { name, source, args }`. Driver: `instantiate_module` expands the
  declaration into ordinary definitions `N.x : ann := spine` fed through `process_def`, so
  the kernel re-checks every expansion. Two non-obvious mechanics: (1) the annotation is
  computed by asking the typechecker to INFER the applied spine in the pre-insert layout —
  inference validates each argument against its domain and returns the concrete
  instantiated type, which passes `process_def`'s universe check; neither term-level
  application to an embedded Pi (ill-typed) nor NbE evaluation (do_apply intentionally
  blocks on VPi) can produce it; (2) the value spine references the source member at
  `idx + 1` because `process_def` front-inserts this very member before checking its body —
  the syntactic spine only needs to be valid for that immediate check. Members expand
  oldest-first with per-member index recomputation; nested members rejected in v1; partial
  instantiation falls out naturally (members stay Pi over unapplied parameters); aliased
  imports reject instantiation (no modules exist under folding). Instantiated names sync
  back via `parser.sync_from_env` so later declarations resolve them.
  Verified: driver tests `run_module_instantiation_typechecks_and_computes`
  (parameterized source, computes), `run_module_instantiation_of_plain_module`;
  `examples/module_params.owl` extended (`NatSemi.twice_id three` → `3`); smoke-tested
  partial application and plain-module case manually; full `cargo test` **227 green**;
  docs/reference.md §13 updated.

- [x] **Module parameters — `module M (A : Type) where ... end` (defs-only v1).** Parser:
  `parse_module_decl` (`src/cubical/parser/mod.rs`) accepts binder lists via new
  `parse_module_binders` (`src/cubical/parser/grammar.rs`, record-parameter style:
  front-inserted into `term_env`, last binder at index 0); `module_params: Vec<Vec<(Name,
  Term)>>` runs parallel to `module_stack`; `Decl::Module` gained `params`. Two de Bruijn
  subtleties handled explicitly: (1) each parsed parameter type is weakened by
  `shift(-1,0)` because it was parsed in a layout containing its own binder while the final
  Pi-chain places it *before* that binder; (2) sibling auto-application
  (`apply_module_params`) computes parameter-variable indices relative to the **current**
  `term_env` depth (`L-1-i` for the i-th declared parameter) since references may sit under
  additional local binders — the first cut used static offsets and was wrong for multi-param
  modules under lambdas. Semantics: every def inside is closed over the params
  (`wrap_with_module_params`: `Pi` on the annotation, `TAbs` on the value — body indices
  already match the leading-binder layout), so consumers instantiate by ordinary application
  (`((Semi.twice_id Nat) two)`); bare sibling refs inside resolve to the qualified global
  applied to in-scope param vars; unrelated globals stay unapplied. Restrictions (clear
  parse errors): no nested parameterized modules; no datatypes/records/imports inside.
  Aliased imports interoperate: module headers are folded as before but their binder scopes
  still open/close around the body (folded-scope pop at `end` when
  `module_params.len() > module_stack.len()`). Kernel/typechecker untouched — wrapped defs
  are ordinary Pi-typed globals. Verified: parser tests
  `parses_parameterized_module_declaration` (exact wrapped shapes),
  `parses_module_param_sibling_autoapplication`,
  `rejects_datatype_inside_parameterized_module`, `rejects_nested_parameterized_modules`;
  driver tests `run_parameterized_module_defs_typecheck_and_compute`
  (computes: `(Semi.twice_id Nat) one` → `2`),
  `run_parameterized_module_rejects_datatype_inside`,
  `run_aliased_import_folds_parameterized_module_member` (plain keeps `Semi.idty`, alias
  folds to `P.idty`); `examples/module_params.owl` + sweep guard; multi-param smoke test
  with value-typed second parameter evaluates correctly; full `cargo test` **225 green**;
  docs/reference.md §13 updated.

- [x] **Unification of same-name imports — provenance-based conflict detection.** The
  driver now threads two registries (`def_sources`/`dt_sources: HashMap<Name, PathBuf>`)
  mapping every imported name to its **defining file's canonical path**
  (`note_imported_def`/`note_imported_dt`, registered per-declaration in
  `process_file_source` with an `origin: Option<&Path>` parameter; `None` for the root
  file). Policy: (1) import-vs-import collisions across **different** files are hard
  `RunError::Import` errors naming both sources and the remedies — silently shadowing used
  to make later declarations depend on import order; (2) re-merges of the **same** file are
  tolerated (diamond imports, several `only [...]` selections of one library) because
  origins track the defining file, not the importer — a transitive merge inside A then a
  direct merge of the same file share one origin; (3) **local definitions may still shadow
  imported names** (innermost-wins), preserving long-standing behavior like defining
  `main` after an import; (4) hiding via `only [...]` suppresses registration entirely, so
  unselected names never participate in conflicts — selection is itself a disambiguation
  mechanism. Content-based definitional-equality unification was considered and rejected:
  stored terms from separate merges normalize with different global-reference anchoring
  (stuck eliminators quote case bodies relative to their captured env), so "definitionally
  equal at merge time" is not reliably decidable without fragile level-mapping; explicit
  `as`/`only` is the documented route instead. Cycle detection also moved to per-canonical-
  path keys (Phase 1). Verified: driver tests `run_same_name_imports_from_different_files_rejected`
  (conflict even for byte-identical texts, three-file layout so only `double` collides),
  `run_diamond_import_of_same_file_tolerated`, `run_conflicting_imported_definitions_rejected`
  (confa transitively merged through confb — single Nat origin — while confb's differing
  `helper` conflicts), `run_conflicting_imported_datatypes_rejected`; existing import tests
  and all lib/example guards unaffected (ring_laws ∩ field_laws = ∅); full `cargo test`
  **218 green**; docs/reference.md §13 updated.

- [x] **Selective imports — `import "f.owl" only [x, M.y]`.** Grammar (`parse_import` +
  new `parse_only_list` in `src/cubical/parser/grammar.rs`) accepts an optional
  `only [a, b.c,]` clause after the path/alias: bracketed comma-separated dotted names,
  trailing comma and empty list allowed; `Decl::Import` gained `only: Option<Vec<Name>>`.
  Driver semantics (**visibility pruning**, `src/cubical/driver.rs`): the imported file is
  processed **fully** (de Bruijn indices are assigned from declaration order at parse time,
  so dropping decls would corrupt every later reference), then each of *its own* declarations
  that is not selected is hidden — defs by **renaming** to a NUL-prefixed unmatchable name
  (`hide_front_def`; names are cosmetic labels, positions are what matter), datatypes by
  **removal** from `env.datatypes` (`prune_datatypes`; lookup is by name). Selection entries
  are dotted paths relative to the file's top level, pre-aliasing (`import_selection_selected`
  strips the forced-alias prefix): entry matches exactly or as module-path prefix, so
  `only [M]` keeps all of module `M`, `only [M.x]` one member. Transitive imports inside the
  selected file are unaffected (their decls bypass this file's pruning hooks). Consequence:
  dependencies must be listed (`only [Nat, add]`, not just `add`) — referencing a hidden or
  dropped name fails loudly at its point of use, never mis-resolves. Dedup key extended to
  `(canonical path, alias, sorted selection)` (`loaded_tag`) so different selections load
  separately; circular-import detection moved to per-canonical-path keys (alias/selection
  keys would miss same-file cycles through different selections). Verified: parser tests
  `parses_selective_import_declaration`, `parses_selective_aliased_import_declaration`,
  `selective_import_requires_bracket_list`; driver tests `run_selective_import_keeps_selected_names`,
  `run_selective_import_hides_unselected_names`, `run_selective_import_module_member_selection`,
  `run_selective_import_avoids_name_collisions` (two libs exposing same-named `helper`
  coexist via disjoint selections); full `cargo test` **214 green**; docs/reference.md §13 updated.

- [x] **Module & import system basics landed (`module M where`, file imports, aliased imports).**
  Commit `a99fe11`. Modules are lexical namespaces over the flat de Bruijn global env:
  `module M where ... end` prefixes every subsequent declaration's name with `M.` (nested
  modules compose: `Outer.Inner.T`), and unqualified references resolve innermost-module-first
  then enclosing modules then top level (`qualified_candidates`/`resolve_dotted` in
  `src/cubical/parser/grammar.rs`). Dotted references (`M.x`, `M.Nat.zero`,
  datatype-qualified constructors `Nested.mk`) resolve through `resolve_dotted`. File imports
  merge whole files recursively into one env (`load_import`, `src/cubical/driver.rs`):
  `import "f.owl"` keeps the file's own names; `import "f.owl" as A` forces the `A.` namespace,
  folding the file's own module segments away. Dedup key is `(canonical path, alias)` so the
  same file can be imported under several aliases; circular imports are detected via a loading
  set. Verified by driver tests `run_with_import_merges_declarations`,
  `run_reports_circular_import`, `run_aliased_import_qualifies_names`,
  `run_nested_modules_and_aliased_folding` and parser tests `parses_import_declaration`,
  `parses_aliased_import_declaration`, `parses_module_declaration`,
  `import_without_string_is_parse_error`; documented in `docs/reference.md` §13.

- [x] **Split the 7,192-line `nbe/mod.rs` into focused submodules.** Pure code motion — no logic changes — along the file's natural section boundaries: `value.rs` (runtime types: `Scope`, `Value`, `Neutral`, closures, `Globals`), `eval.rs` (`eval_nbe`, `subst_interval_var`, `eval_system`), `elim.rs` (`do_force/apply/papp/fst/snd/proj/elim`, `reduce_con_at_endpoint`, `stuck_elim`), `transport.rs` (`do_transport`, per-shape `transport_*`, `uses_var_at_level`, `transport_term_fallback`), `hcomp.rs` (`do_hcomp/comp/fill/hfill`, tube-coherence helpers), `quote.rs` (`quote` family + depth guard, `level_to_var`), `meta.rs` (`meta_mentions`, `try_solve_meta`, `zonk`, term-children walkers), and `util.rs` (cross-cutting helpers: `value_to_dnf`, `value_to_endpoint`, `do_equiv_fwd`, `equiv_dom_value`). `mod.rs` is now a ~160-line facade: module docs, re-exports preserving the historical flat API (`crate::cubical::nbe::*` unchanged for all external callers — none needed editing), and the top-level entry points (`normalize`, `nbe_eval`, `nbe_eval_with_globals`, `nbe_eval_ctx`). Cross-module items that were private use `pub(super)` so nothing new leaks into the crate API; the re-export block carries an annotated `#[allow(unused_imports)]` because some exports are external/test-only API in a binary crate. Also deleted the dead helper `find_system_entry_at_endpoint` (zero callers). The nbe unit tests moved verbatim to `tests.rs` (`#[cfg(test)] mod tests`). Verified: `cargo build` clean (0 warnings), `cargo fmt --check` clean, full `cargo test` **207 green** (including the slow field/ring suites), spot checks `cargo run -- check examples/{nat,nat_path_algebra,partial_elements}.owl` OK; rust-analyzer-db rescanned.

- [x] **Consolidated thread-local state into a single `Session` struct.** All 14 scattered `thread_local!` blocks (across `nbe/mod.rs`, `typechecker/mod.rs`, `typechecker/errors.rs`, `typechecker/termination.rs`, `equality.rs`, `nbe/trace.rs`) are now behind one `thread_local! { static SESSION: RefCell<Session> }` in `src/cubical/session.rs`. The `Session` struct holds all mutable shared state: NbE globals/cache/depth guards, metavariable solutions/names/expected types, typechecker flags (`skip_plam_endpt`, `skip_guard`, `current_def`), elim-case recursion depth, error positions, and debug trace. Public accessor functions (`set_current_dts`, `current_dts`, `set_current_globals`, `fresh_meta_id`, `should_skip_guard`, etc.) preserve the existing API — callers continue to use the same function names, which now delegate to `Session` fields. This eliminates hidden coupling between modules (the typechecker and NbE evaluator no longer communicate through separate implicit channels), removes the error-prone manual save/restore patterns for thread-locals, and makes all shared state visible in one place. 9 files changed, net -123 lines. Full `cargo test` **207 green** (previously 207). Future work: thread `&mut Session` through function signatures to make state explicit in the call graph.

- [x] **Square/cell-constructor endpoint reduction (`cube3 @ i0 @ i0 @ i0` → `base`).** `src/cubical/nbe/mod.rs` now reduces higher constructors applied at concrete endpoints to their faces at eval time, closing the gap where the `TSqCon`/`TCellCon` eval arms built `VSqCon`/`VCellCon` values that quoted back neutrally (the `do_papp` boundary branches were unreachable for parsed `square @ i0 @ i1` / `cube3 @ i0 @ i0 @ i0`, and the `VCellCon` branch mis-applied the remaining interval args in reverse). Changes: (1) the `TSqCon` eval arm reduces at a concrete `r` (`sq @ 0 @ s = face_j0 @ s`) or `s` (`sq @ r @ 0 = face_i0`, independent of `r`), (2) the `TCellCon` eval arm reduces when the *outermost* interval arg is concrete, applying the outermost face pair and the remaining interval args outermost-first (matching the typechecker's `reduce_pcon_endpoints_dt`), (3) the `do_papp` `VCon` branch now recognizes square/cell constructor references too (a bare `square` face evals to `VCon` and `square @ i0` is `face_j0`), so the PApp chains the eval arms build keep reducing all the way to a point, and (4) the `do_papp` `VCellCon` branch applies the remaining ivars in parsed order (`ivars[1..]`) instead of `rev().skip(1)` and is guarded like `reduce_con_at_endpoint`. Both eval arms are *term-based* (mirror the typechecker): faces are substituted with the **original** args and the result is evaluated in the **same** env, so open args keep their levels — the earlier pcon regression mechanism (empty-scope quote/eval renumbering free-variable levels) does not apply here; only faces referencing the datatype's parameters (levels ≥ arity in the face scope, absent from the eval env) are left neutral. The old value-based `reduce_pcon_at_endpoint` was generalized to `reduce_con_at_endpoint` (pcon/sqcon/cellcon faces; closed-args + no-param guard) and now serves the `do_papp` `VPCon`/`VCon` branches, while the `TPCon` eval arm switched to the same term-based scheme, so `mer n @ i1` with an *open* `n` now reduces too (`open_arg (suc zero)` → `(sso 1)`). Verified: `/tmp/endpt.owl` `main : Cube = base`; all 8 square/cube endpoint combos reduce to `base`; a distinct-faces cube confirms face *selection* (`c3 @ … @ i0 = a`, `c3 @ … @ i1 = b`); mixed asymmetric cells (`cube3 @ i0 @ i1 @ i0 = base`) match the docs; regressions green (`test_sq.owl` Trunc case body OK, `pcon_flow.owl` `(sso 0)`, `refined_hit_cases.owl`, `torus_id.owl`, `square_constructors.owl`, `cell_constructors.owl`). Guarded by new driver test `hit_constructor_endpoints_reduce_to_faces` (9 endpoint combos assert the normal form is `base`). Full `cargo test`: **200 green**; `scripts/verify.sh --quick` green. Docs: `docs/reference.md` §5 "Endpoint Application" + corrected the square-endpoint table comments (the boundary at `r=0` is `face_j0`, etc.).

- [x] **Pcon endpoint reduction (`mer 0 @ i1` → `sso 0`).** `src/cubical/nbe/mod.rs` now reduces path-constructor values applied at concrete endpoints: the `Term::TPCon` eval arm and `do_papp` (new general-arity `VCon` branch + new `VPCon` over-application branch) route through `reduce_pcon_at_endpoint(globals, global_offset, data, con, args, endpoint)`, which looks up the constructor's `PConSig` in `current_dts()`, quotes the args, substitutes them (highest index first) into the matching face (`face0` for `i0`, `face1` for `i1`), and evals the face in an empty scope. Two soundness guards restrict reduction to the faithful case: the face must not reference the datatype's parameters (`max_var(face) < args.len()`), and every argument must be **closed** (`max_var(arg) < 0`) — open arguments stay neutral, because empty-scope quote/eval renumbers free-variable levels while the surrounding comparison contexts derive levels from their own terms (a regressing example: `/tmp/test_sq.owl`, `Trunc | trunc a b i => <j> trunc a b @ j`, failed with `Type mismatch expected: (inc a) got: (inc b)` until the open-arg reduction was disabled). Verified: `test_sq.owl` OK again, `/tmp/pcon_flow.owl` `main : SuspX = (sso 0)`, `test_rec.owl` `t14 = (sso 1)` (previously stuck `(mer 1 @ 1)`), `refined_hit_cases.owl` and `cell_constructors.owl` unchanged; full `cargo test` **199 green**. Docs: `docs/reference.md` §7 "Endpoint Application".

- [x] **Nested constructor patterns — Phase 2 (HIT-case refinement).** Path-constructor HIT cases can now refine their ordinary argument slots with nested constructor patterns (`mer (suc m) i => <j> suc m`). Parser (`grammar.rs`): `is_single_interval_path_con` gates refinement to single-interval `pcon` heads; `nested_head_datatype(con, allow_pcon)` parameterized; `compile_nested_arms` emits `refinements: Some(...)` for refined pcon cases (flat cases stay `None`). Typechecker (`typechecker/mod.rs:~2216`): refined bodies are destructured as `TElim(_, cases, TVar(slot))`, the motive rebuilt as `TAbs("z", subst(slot+1, TVar(0), shift(1,0,expected_body_ty)))`, and the rebuilt elim rechecked with `SKIP_PLAM_ENDPT` **off** so each leaf's PLam rule enforces endpoint coherence against the refined binder (flat pcon path unchanged). NBE `do_elim` (`nbe/mod.rs:~1345`): case bodies are compiled with the case's interval binder(s) as phantom term slots at the **base** of the environment (below the ordinary args) — `quote_cases` pushes `binders.len()` values and `IClosure.apply_interval_value` pushes a `VInterval` slot — but `do_elim` chained only the ordinary args, so any body referencing an ordinary arg (`<j> n` → `TVar(2)`) resolved one binder too high and stayed stuck. VPCon now pushes `[r] + args.rev()`, VSqCon `[s, r] + args.rev()` (innermost first), VCellCon `ivars.rev() + args.rev()`. Verified: `examples/refined_hit_cases.owl` (flat arm using its arg, `mer zero`/`mer (suc m)` refined arms, recursive refined arm) evaluates to the right values (`1`, `0`, `(mer 2 @ 1)`, `(mer 1 @ 1)`); deliberately incoherent refined arms are rejected on open scrutinees (`Type mismatch expected: (suc m) got: 0`); sqcon-with-args (`pair a b r s => <i> <j> pair a b @ i @ j`) and cellcon paths still reduce. Guarded by driver tests `refined_hit_cases_example_checks` (64 MiB stack) and `refined_pcon_arms_reject_incoherent_endpoints`; full `cargo test` 197 green, `scripts/verify.sh --quick` 193 green.

- [x] **`examples/field_demo.owl` debug-build stack overflow — root-caused and fixed.** The 64 MiB test-thread stack (and the default-stack crash under `cargo run -- check`) was *not* deep recursion: gdb showed only **~154 frames** at the overflow, but each `infer_dt`/`check_dt` frame costs **~176 KiB in unoptimized builds** (debug codegen spills the whole match's temporaries — `Term`/`TypeError` are only 96/152 bytes, so this is pure opt-level-0 frame bloat). Peak ≈ 27 MiB > the 8 MiB default → overflow. Release builds shrink the frames to a few KiB and run `field_demo` on a **512 KiB–1 MiB stack** (default 8 MiB is fine; 2m33s). The `by field` proofs are large (up to ~392k nodes for `frac_add`) but **wide and shallow** (max term depth ≤ 88), and the checker recursion stays shallow (~150 frames); `eta_eq` isn't even reached (normal-form comparison succeeds syntactically). So: **no dynamic allocation and no kernel/typechecker refactor is needed** — the requirement is purely a debug-build artifact. Also fixed a real inefficiency found along the way: `debug_scope!` eagerly evaluated `&format!(...)` (walking the full term via `show_term`) on **every** `check_dt`/`infer_dt` call even with debugging off; it now only formats when `is_active()` (`DebugScope::inactive()`). Verified: release `field_demo` on default stack OK and 2m33s→2m10s; debug driver test `field_demo_example_checks` 296s→271s; `scripts/verify.sh --quick` green (191 tests); `--debug` output unchanged. Documented: heavy `by field`/`by ring` proofs in **debug** builds need a larger stack (`ulimit -s 65536` or the 64 MiB test-thread pattern); release builds need no special stack.

- [x] **Nested constructor patterns — Phase 1 (parser-side compilation, kernel untouched).** `Pat::Var/Con` AST in `src/cubical/parser/patterns.rs`; `parse_match_cases` in `grammar.rs` is now a two-pass compiler: pass A scans each arm's leading column (or-patterns, `as`, record patterns) into `Vec<(Vec<Pat>, Option<Name>, Term)>`, pass B routes record arms byte-identically, flat (all-var) arms to the same flat `ElimCase`s as before, and nested arms to `compile_nested_arms`/`compile_columns`, which group same-head arms (first-appearance order) and compile nested constructor patterns into chains of nested `TElim`s whose motives plug the eliminated argument into the case's expected type exactly as the typechecker computes it (`shift(arity+extra_shift, 0, motive)` applied to `TCon(con, [TVar(arity-1-k+extra_shift)])`, columns at slot `arity-1-k+extra_shift`, refined columns reindexed `rest_slot + sub_arity`; `extra_shift = 1` when an `as`-binder sits at index 0). Two subtleties surfaced during bring-up: (1) `parse_pattern_after_con` originally consumed arguments greedily, so a zero-arity constructor like `nil` swallowed its siblings (`cons nil xs` gained a bogus extra arg — silent wrong parse); it now consumes exactly `arity` arguments for known ordinary constructors and falls back to greedy only for interval-binder (path/square/cell) constructors and unknown heads (no datatype env). (2) Nested `Pat` args are read as constructor patterns via `find_constructor` (the audited backward-compat change: `suc zero` now really matches the literal `zero`), and `headTwo`-style examples confirmed that nesting a pattern in a slot whose type is a *different* datatype is rejected by the kernel's `MissingCase` — that is sound, so the example avoids it. Phase 1.3's completeness check (`check_match_completeness`) fires only when the scrutinee is an open variable (`Term::TVar`), because the kernel reduces eliminators over closed constructor values, making partial closed matches (e.g. `stress_as_patterns.owl`) legal; the typechecker's `MissingCase` remains the backstop for sub-level gaps. Phase 1.4 rejects mixed variable+constructor columns ("mixed variable and constructor patterns in the same column" / "...for the same constructor", the latter needed because flat and nested arms land in different passes) and inconsistent `as`-bindings across merged arms. Verified: 8 new parser unit tests (62 total), `examples/stress_nested_patterns.owl` (nested `suc`/list/`Tree` head-position patterns, as+nested, or+nested, merged heads) with 15 evaluation checks all computing the right values, driver guards `nested_patterns_example_checks` (64 MiB stack), `nested_patterns_reject_mixed_columns`, `nested_patterns_reject_incomplete_match`, and `bad_examples/{incomplete_nested_match,mixed_pattern_columns}.owl`; the `all_example_files_check` sweep, the 8 quick driver regression tests, `stress_mul_algebra` and `field_laws` stay green, and `field_demo` still passes on its 64 MiB stack thread (296 s, unchanged pre-existing stack-size behaviour). 191 tests green.

- [x] Multiplicative algebra over `Nat` — `examples/stress_mul_algebra.owl` now proves the classic hard theorems (`_owl_mul_zero_r`, `_owl_mul_suc_r`, `_owl_mul_one_r`, `_owl_mul_comm`, `_owl_mul_add_r` right-distributivity, `_owl_mul_assoc`, `_owl_mul_double`, and the consumer lemma `_owl_double_double`), composing the additive laws with `by omega` for the definitional / direct-lemma-instance subgoals. One contained kernel fix in `src/cubical/equality.rs` (the eliminator-congruence arm of `eta_eq`): a stuck elim suspends its case bodies, so a reducible global application (e.g. `mul b c`) substituted into a case body is never reduced by whole-term normalization — leaving `(mul b) c` in the normal form while the same value entered as an eagerly-evaluated function argument appears folded. Each elim case body is now normalized **once** in isolation and compared structurally, falling back to the original raw comparison when the single pass does not converge (re-normalizing recursively would unfold recursive definitions one level per pass and never reach a fixed point — the transient stack overflow this fix replaced). Covered by `stress_mul_algebra_example_checks` in the driver (runs on a 64 MiB stack since the deep elim/hcomp normal forms exceed the default 2 MiB test-thread stack); all 175 tests stay green.

- [x] hcomp-based transitivity on the pristine kernel — The full Nat lemma suite typechecks and computes with **zero kernel changes** (`src/cubical/typechecker/mod.rs` left byte-for-byte original). The suite: `_owl_cong_suc`, `_owl_sym`, hcomp-based `_owl_trans` (`fun a b c p q => <i> hcomp Nat [~i => <j> a, i => q] (p @ i)`), `_owl_add_0_r`, `_owl_add_suc_r`, `_owl_cong_add_r`, `_owl_add_comm`, `_owl_cong_add_l`, `_owl_add_assoc`. The real blockers were **surface-syntax** constraints, not the kernel: (1) integer literals `0`/`1` parse as the interval endpoints `i0`/`i1`, so Nat terms must use the `zero`/`suc` constructors (see `src/cubical/parser/grammar.rs`, `TokenKind::Int`); (2) `forall` is only recognized at term top-level, so it cannot follow a `->` — all binders must be declared before the arrow chain (`forall (a : Nat), forall (b : Nat), Path Nat a b -> ...`). An earlier experiment that normalized hcomp faces inside `check_faces` was **reverted**: the kernel already handles interval-variable hcomp faces soundly via `check_dt`'s infer → `nbe_eval`-normalize → retry path (the raw-face `check_faces` fallback error is swallowed, then cube-normalized faces pass the sound checks). Verified with `owl check` and `owl run` (`add_comm 2 3 @ i1 = 5`, `add_assoc 3 2 3 @ i1 = 8`, trans of refl paths `@ i1 = 1`); all 169 tests stay green.

- [x] Idempotent normalization with global definitions — `nbe_eval_ctx` now builds the evaluation environment from **local binders only**; global references resolve through the global definition value vector (`global_offset + (i - env.len())`) instead of being placed in the environment. Keeping globals out of the env is load-bearing: a stuck eliminator created during evaluation captures the env, and `quote_case_body` re-anchors a raw case-body global ref as a *reference below the quoting frame* precisely when the ref lands beyond `env.len()`. If globals were in the env, those refs would land inside `env.len()` and get inlined by re-evaluation, re-opening recursive definitions (e.g. `add`'s case body calling `add`) on every normalization pass — unbounded term growth that exhausted eta-equality fuel (`EtaFuelExhausted`). With the locals-only env, normalization is idempotent: quoting a term twice yields the same normal form. Verified on a `Path Nat ((add_0_r n) 0) n` recursive proof that previously failed at fuel exhaustion; all 36 `examples/*.owl` and 169 tests stay green.

- [x] PathP (dependent path types) — Added as syntactic sugar over TPath. `PathP (<i> A i) u v` parses to `TPath(PLam("i", A i), u, v)`. Type families work correctly with endpoint checking.

- [x] General systems for hcomp/comp/fill/hfill — Multi-face system syntax `[phi => tube, ...]` using `=>` (FatArrow) separator. Old single-face syntax `comp A phi tube base` still works (desugars to single-entry system). The `System` type is `Vec<(Term, Term)>`. Top-face reduction applies tube at i1 (not raw VPLam). Constant type families handled correctly for comp/fill. Compatibility checking delegated to face-by-face `check_faces` calls.

- [x] Parameterized inductive types — `TData(Name, Vec<Term>)` across all files. Parser handles `(A : Type)` parameter binders. Two-phase parameter inference in typechecker. Constructor arg types reference params via de Bruijn indices.

- [x] Higher inductive types (HITs) with path constructors — Parser supports `[ face0 , face1 ]` syntax for path constructors. Typechecker checks path constructor case bodies as PLam against TPath with correct endpoints. `reduce_pcon_endpoints_dt` reduces path constructors at endpoints. Fixed de Bruijn scope bugs: parser binder ordering, face term scope in expected_body_ty, and subst-based arg substitution in reduce_pcon_endpoints_dt.

- [x] Better error cascade in check_dt — Added specific `check_dt` arms for `THComp`, `TComp`, `TFill`, `THFill`. Expected type is checked first (via cumulativity) before delegating sub-term checking to `infer_dt`. On `infer_dt` failure, retries with `nbe_eval` to handle cases where the Kan operation reduces. This gives clearer error messages for type mismatches while preserving correct handling of face compatibility.

- [x] Truncation types (isProp, isSet, isGroupoid) — Parser-level desugaring of `isProp A`, `isSet A`, `isGroupoid A` into nested Pi/Path types. `isProp A` desugars to `(x : A) -> (y : A) -> Path A x y`. `isSet A` desugars to `(x : A) -> (y : A) -> (p : Path A x y) -> (q : Path A x y) -> Path (Path A x y) p q`. `isGroupoid A` desugars similarly with 6 binders.

- [x] Set-quotients / quotient types — Demonstrated via HITs with path constructors. Pattern: define `MyInt` with point constructors and a path constructor `squash` that identifies two points. Path application (`squash @ i0`, `squash @ i1`) accesses endpoints. Eliminators must respect path boundaries.

- [x] Square constructors (2D HIT cells) — `[[ face_i0, face_i1, face_j0, face_j1 ]]` syntax for square constructors in HITs. Parser creates `TSqCon(d, con, args, r, s)` terms. `infer_dt` builds nested PathP type `PathP (<r> PathP (<s> TData(d)) fi0 fi1) fj0 fj1`. `check_dt` handles TSqCon against TData by verifying data type match and interval arg validity. `SKIP_PLAM_ENDPT` flag skips boundary checks for HIT case bodies. Applied `apply_literal` for IVar-based endpoint checks. Identity function on Torus typechecks correctly.

- [x] Partial elements / Cubical Subtypes — `[_ | phi] A` syntax for partial elements. Added `TPartial(phi, A)` term constructor and `VPartial` value constructor. Supports both bracket syntax `[_ | phi] A` and keyword syntax `Partial phi A`. Type inference: `TPartial(phi, A) : U_n` when `A : U_n`. NbE reduction: `TPartial(i1, A)` reduces to `A`. Parser, pretty-printer, equality, positivity checker, and apply_literal all handle the new constructor.

- [x] Fix 3 pre-existing example errors — `hits_parameterized.owl`, `stress_glue_hcomp.owl`, `stress_transport.owl` now pass (112 tests, 18 examples all green):
  - PLam boundary check shift: Added `shift(-1, 0, ...)` to `body_at0`/`body_at1` in PLam check (matching the existing shift in path constructor endpoint check).
  - Parser: Path constructor space-application now extends TCon args instead of wrapping in TApp chains, so `@ interval` correctly creates TPCon.
  - `reduce_pcon_endpoints_dt` TApp chain: Now walks TApp chains to find underlying TCon for path constructor endpoint reduction.

- [x] Debug improvements (`-d` flag) — `process_def` logs definition name on entry. `ContextualError` wraps TypeError with definition name. Trace printing distinguishes success/error cases. Debug scope output shows term, expected type, and context depth.

- [x] Prop and SSet universes — `TProp` (impredicative, at U0) and `TSSet` (predicative, at U1) added to Term/Value enums. Prop is closed under Pi/Sigma/Path when both sides are Prop (impredicativity). SSet is predicative. Parser, pretty-printer, NbE, positivity, and cumulativity all handle the new constructors. `TUniv(0)` cumulates into `TProp` via cumulativity check.

- [x] Universe lifting/lowering — `TLower(t)` and `Tlift(t)` (lower/lift) for moving terms between universe levels. Parser, pretty-printer, NbE, equality, and positivity all handle the new constructors. `lower` at U0 reduces to identity.

- [x] Cumulativity for inductive types — `TData(d, ps) <= TData(d, ps')` when names match and parameters are checked covariantly. `TPath` cumulativity in all three components. Implemented in `cumulativity_check`.

- [x] Termination / Guard checking — Structural recursion guard in `termination.rs`. Recursive calls in TElim arms must pass a case binder (de Bruijn index < binder_count) as the scrutinee. Rejects non-structural recursion with `TerminationViolation` error. Wired into `infer_dt` before return type checking.

- [x] Induction-induction (mutual inductive types) — `inductive A where ... | with inductive B where ...` syntax. `Decl::DataMutual(Vec<Datatype>)` variant. Forward references: all mutual datatypes registered before constructor parsing. Driver `process_data_mutual` does two-phase processing (register all, then check constructors). Parser `sync_from_env` handles `DataMutual`.

- [x] Induction-recursion — `inductive D where ... | with f : T := e` syntax. `Decl::DataWithFunc { dt, func_name, func_ty, func_val }` variant. Function name added to parser `global_env` for self-reference. Driver `process_data_with_func` calls `process_data` then `process_def`. Parser `sync_from_env` adds func_name to global_env for subsequent declarations.

- [x] Well-founded recursion — `by_wf` annotation on `def` disables structural guard check via thread-local flag. Parser uses `stop_at_by_wf` to correctly parse the annotation. Wired in `process_def` and `termination.rs`.

- [x] Coinduction — `Delay A` type, `Next` constructor, `Force` destructor with `Force (Next x) = x` beta rule. Added `TDelay`/`TNext`/`TForce` to Term, `VDelay`/`VNext`/`VForce` to Value, `NForce` to Neutral. Full pipeline: shift/subst/max_var, pretty-printer, parser (prefix operators), NbE eval/quote, typechecker (Delay A : U_n when A : U_n, Force : Delay A -> A), equality, positivity. Parser `Delay` in `parse_atom`, `Next`/`Force` in `parse_prefix_or_atom`.

- [x] Stress test and documentation — `examples/stress_mutual_and_ir.owl` exercises all 5 new features. `examples/stress_hit_elimination.owl` exercises nested pattern matching (4-level deep), dependent elimination, parameterized HITs, and hcomp/fill. `docs/reference.md` updated with Prop/SSet, lift/lower, mutual inductives, induction-recursion, termination guard, and worked examples.

- [x] Parser nested pattern matching — Column-based `|` nesting: records column of first `|` in match, breaks when `self.peek().col < my_col`. Fixed infinite recursion in termination checker via `motive_targets_datatype` + `check_body_guard` else branch. Nested patterns work across all HIT types.

- [x] Safe `CURRENT_DTS` — Replaced `Cell<Option<*const [Datatype]>>` raw pointer with `RefCell<Vec<Datatype>>` in thread-local. Eliminates all `unsafe` from `nbe/mod.rs`.

- [x] Type errors point at the offending variable — The parser records the source position of every variable use (and each definition name) while parsing, exposing them via `ProgramParser::take_decl_positions`. The driver accumulates these across the whole program and installs them into the typechecker's thread-local `DECL_NAME_POS` table before checking each declaration. `err_pos` (the `pos` fields on `TypeError` variants) now resolves the most-local de Bruijn variable of the offending term to a real `line:col`, so messages print e.g. `Expected a Π-type, but found: Nat  at 5:43`.

- [x] **Phase 4a: Threaded `&mut Session` through 62 NbE functions.** Converted 62 public functions in `nbe/mod.rs` to take `session: &mut Session`, updated 29 method calls and 659 internal call sites. Zero E0061 errors. All functions that touch mutable session state (eval cache, depth guards, metavariables, globals, datatypes) now receive session explicitly. Build: 0 errors. Tests: 207/207 pass.

- [x] **Phase 4b: Threaded `&mut Session` through all external callers.** Modified 150 function signatures across 8 external files (typechecker/mod.rs, typechecker/errors.rs, equality.rs, tactics.rs, field.rs, ring.rs, omega.rs, driver.rs, env.rs, parser/mod.rs, parser/grammar.rs) and inserted `session` at 1054+ call sites. Key fixes: cross-file name collisions (reify_add/reify_mul), parser carries `&'a mut Session` to avoid RefCell re-entrancy, `zonk`/`try_solve_meta`/`err_pos`/`set_skip_plam_endpt`/`set_meta_expected`/`get_meta_name`/`get_meta_expected` all converted to session methods, `show_term` uses `current_session()` raw pointer for meta name lookup without RefCell re-borrow. Cleaned up all 35 old free-function accessors from session.rs (dead code). Build: 0 errors, 0 warnings. Tests: 207/207 pass.

---

## Remaining — Open Items by Category & Priority

> Legend: 🔴 High priority · 🟡 Medium priority · 🟢 Low priority
> (Priority reflects impact on soundness/core usability vs. polish/ecosystem breadth.)

### A. Core Type Theory Soundness Gaps 🔴

These extend already-partially-implemented features (cumulativity); until closed, some legal
subtyping relations are simply not recognized by the checker.

- [x] **Cumulativity for Sigma/Pi types** — extend the existing universe-level cumulativity check to Σ/Π. Π is contravariant in the domain / covariant in the codomain; Σ is covariant in both. Implemented in `cumulativity_check` (see `src/cubical/typechecker/mod.rs`), with tests in `src/cubical/typechecker/mod.rs` and `src/cubical/parser/tests.rs` and a worked example in `examples/cumulativity_sigma_pi.owl`.
- [x] **Cumulativity for record types** — extend cumulativity to desugared record (single-constructor) types. Covered by the `TData` (covariant parameters) rule, since records desugar to single-constructor inductives; see `cumulativity_check` and `examples/cumulativity_sigma_pi.owl`.
- [x] **Variance-aware datatype parameter cumulativity** — the `TData` cumulativity rule now respects per-parameter variance (see `compute_param_variances` in `src/cubical/syntax/positivity.rs`): covariant parameters are checked covariantly, contravariant parameters (occurring only in arrow domains) are checked contravariantly, and invariant parameters (occurring both positively and negatively) require definitional equality. Without this, `Bad U0 ≤ Bad U1` typechecked for a `Bad A` whose parameter occurs negatively. Variance is a least fixed point over the datatype environment, so it propagates through nested datatype applications and mutual definitions. Unit tests in `src/cubical/syntax/positivity.rs` and `src/cubical/typechecker/mod.rs`; integration tests in `src/cubical/parser/tests.rs`.

### B. Decision Procedures / Proof Automation 🔴

The single highest-leverage category for day-to-day proof productivity — these let users
discharge routine algebraic/arithmetic goals in one line instead of writing them by hand.

- [x] **Omega / Linear arithmetic** — decision procedure for linear arithmetic over Nat/Int. *(🔴 — most general-purpose payoff; underlies many other proofs.)* Implemented in `src/cubical/omega.rs`: `by omega` proves `Path Nat u v` goals by (1) definitional reflexivity (normalization unfolds `add`/etc. on constructor-headed arguments) and (2) direct application of a previously verified global lemma to the context's variables, both re-checked by the kernel. Worked example in `examples/omega_demo.owl`. *Remaining: on-demand induction synthesis (structural recursion via the current definition). `Int` support landed — see §H3.*
- [x] **Ring solver** — decision procedure for ring identities (normalize + compare polynomial forms). *(🔴 — classic high-value tactic, e.g. Coq/Agda's `ring`.)* Implemented in `src/cubical/ring.rs`: `by ring` proves `Path Nat u v` goals by normalizing both sides to polynomial normal form over the commutative semiring over `Nat` (`add`/`mul`/`zero`/`one`, recognized by the shape of the normal forms their eliminators unfold to) and, when the normal forms agree, building a proof tree by applying ring laws resolved from the context. `lib/ring_laws.owl` supplies the required law names (`add_comm`, `add_assoc`, `add_0_l/r`, `mul_comm`, `mul_assoc`, `mul_1_l/r`, `mul_0_l/r`, `mul_add_l/r`) and the structural lemmas (`trans`, `sym`, `cong_add_l/r`, `cong_mul_l/r`); `examples/ring_demo.owl` exercises it. The generated proof is a raw law-application tree that the kernel re-checks; the structural-recursion guard is skipped for ring output because law bodies unfold to elims on compound neutral scrutinees in the normal form. The final blocker was an ill-typed `trans` in `expand_single` — its proof chain already landed on `sum_term(products)`, but a trailing `sum_concat` step re-wrapped the LHS with an extra `add _ zero`, so the emitted `trans` mismatched the chain's actual endpoint and the kernel re-check normalize-and-retry loop overflowed the stack; dropping the redundant step fixed all three demos. *Remaining: `Int`/additive-group support (neg/sub).* Abstract-ring support (`by ring with C`) landed as part of the H1 work — see §H.1.
- [x] **Group solver** — decision procedure for group identities (associativity, identity,
  inverses). *(🟡)* Landed as `by group with G` over an abstract `Group A mul inv one`
  record (free-reduction word decision + kernel-checked law-application trees); see the
  section-B log entry at the top of this file and `docs/reference.md`. This also lands the
  group-solver half of H3.
- [x] **Field solver** — decision procedure for field identities (ring + division/inverse
  reasoning). *(🟡)* Landed as part of H2 (`by field with F`, lib/field_laws.owl,
  examples/field_demo.owl) — see §H.2; recorded here so section B reflects reality.
- [x] **Decision procedure for propositional equality** — automate
  reflexivity/symmetry/transitivity chains. *(🟡)* Landed as `by eq`: reflexivity closure,
  single-hypothesis use in either orientation (inline symmetry), and BFS chaining through
  context hypotheses composed via a context-provided `trans`/`_owl_trans` lemma; see the
  section-B log entry at the top of this file and `docs/reference.md`.

### C. Pattern Matching 🟡

- [x] **Nested constructor patterns** — e.g. `suc (suc zero)` matching a literal 2 (requires a full pattern AST rather than the current flat-binder matching). *(🟡 — meaningful ergonomics win, moderate implementation cost.)* **Phase 1 (parser-side) and Phase 2 (HIT-case refinement) are DONE.**

  **Plan (agreed 2026-08-10, user-approved):**

  *Phase 1 — parser-side compilation (ordinary constructors, kernel untouched).* ✅
  1. ✅ Pattern AST in `src/cubical/parser/patterns.rs`: `Pat::Var(Name)` / `Pat::Con { con, args: Vec<Pat> }`; `parse_match_cases` (`grammar.rs:1274`) does a two-pass scan of each arm's leading column into `Vec<(Vec<Pat>, Option<Name> /* as_name */, Term /* body */)>`, resolving constructor heads and argument patterns by name via `find_constructor`.
  2. ✅ Compile step: group arms by constructor head → same-head groups merge (vars nest into a nested eliminator); for each constructor `con` with arity `a`, one `ElimCase` (`binders = [v0..v_{a-1}]`, a nested-con slot bound as a `""`-phantom) whose body is the nested-`TElim` chain from `compile_columns`:
     `nested(k) = TElim(TAbs(v, TApp(shift(k,0,motive), TCon(con))), cases, TVar(k + extra))`
     — each nested elim adds exactly one binder above its body; refined-column scrutinee `TVar((a-1-k)+extra+n_refined_before)`; De Bruijn-consistent (`extra = 1` when an `as`-binder sits at index 0, mirroring the typechecker). Flat (all-var) and record cases emit byte-identical `ElimCase`s (source order preserved), so `parses_match` etc. are unchanged.
  3. ✅ Parser completeness check (`check_match_completeness`): infer scrutinee datatype from constructor heads; require full constructor coverage; dedicated `ParseError` "incomplete pattern match: missing case for `<con>`"; fires only when the scrutinee is an open variable (closed matches may be partial — the kernel reduces them); skipped when heads resolve inconsistently (typechecker `MissingCase` remains the soundness backstop).
  4. ✅ Mixed var+con columns inside the same head group → parse error (also the flat-vs-nested same-constructor case, via `flat_heads` tracking); inconsistent as-names across merged groups → parse error.
  5. ✅ Tests: 8 parser unit tests (nested / deep-nested / multi-arg `cons x (cons y zs)` / as+nested / or+nested / merged heads / flat-identical / rejections); `examples/stress_nested_patterns.owl` + driver test `nested_patterns_example_checks` (64 MiB stack); `bad_examples/incomplete_nested_match.owl` + `bad_examples/mixed_pattern_columns.owl` + driver assertions.

  *Phase 2 — HIT-case refinement (kernel change, user-chosen).* ✅
  1. ✅ `ElimCase.refinements: Option<Vec<Option<Vec<Name>>>>` marker field (contract doc on the field, `src/cubical/syntax/mod.rs`): `Some(v)` for path/square/cell constructor cases with one entry per ordinary argument (`Some(leaf_binder_names)` for nested `Pat::Con` slots, `None` for variable slots), `None` for flat cases; refined case bodies are `PLam`-wrapped over the nested `TElim` chain. Plumbed through `shift_cases`/`quote_cases`/`quote_case_body`/`subst_interval_var`. Parser (`grammar.rs`) gates refinement on `is_single_interval_path_con` (single-interval `pcon` heads only; sub-constructor slots stay ordinary-constructor-only); `nested_head_datatype(con, allow_pcon)` parameterized. Flat cases emit byte-identical `ElimCase`s (still kernel-identical).
  2. ✅ Typechecker refined-pcon branch (`typechecker/mod.rs:~2216`): destructures `TElim(_, elim_cases, TVar(slot))` from the case body, rebuilds the motive as `TAbs("z", subst(slot+1, TVar(0), shift(1,0,expected_body_ty)))`, and rechecks the rebuilt elim with `SKIP_PLAM_ENDPT` **off** so each leaf's PLam rule enforces endpoint coherence against the refined binder (flat path unchanged: `SKIP_PLAM_ENDPT` on + manual `reduce_pcon_endpoints_dt`/`require_equal_endpt`).
  3. ✅ NBE `do_elim` env-layout fix (the actual blocker): parsed/typechecked case bodies place the case's interval binder(s) as phantom term slots at the **base** of the environment, below the ordinary args; `do_elim`'s pcon/sqcon/cellcon branches previously chained only the ordinary args, so any case body referencing an ordinary arg resolved one binder too high and got stuck. VPCon now pushes `[r] + args.rev()`, VSqCon `[s, r] + args.rev()` (innermost first), VCellCon `ivars.rev() + args.rev()` — matching `quote_cases` (pushes `binders.len()` values) and `IClosure.apply_interval_value`. Follow-up: `do_papp`/NBE now reduce `VPCon`/`TPCon` at concrete endpoints (see the Phase 2.1 log entry below).
  4. ✅ Docs/examples: `examples/refined_hit_cases.owl` (flat arm referencing its arg, refined `mer zero`/`mer (suc m)` arms, recursive refined arm) + driver guard `refined_hit_cases_example_checks` (64 MiB stack) + negative driver test `refined_pcon_arms_reject_incoherent_endpoints` (open-scrutinee incoherent leaf rejected: `Type mismatch expected: (suc m) got: 0`). Full `cargo test`: 197 green; `scripts/verify.sh --quick`: 193 green. `docs/reference.md` note added (refined HIT-case patterns §7 + endpoint application).

  *Backward compat note:* no existing owl example/library pattern binder collides with a constructor name (audited), so constructor-named identifiers in pattern position becoming constructor patterns is safe; behavior change to document.

### D. Module & Import System 🟡

Needed for organizing larger codebases/libraries; not blocking for single-file examples.

- [x] `module M where ...` — basic namespace declaration. *(🟡)* Implemented in commit
  `a99fe11` (see the implementation-log entry at the top of this file); remaining §D work:
  module parameters/instantiation, selective imports, same-name unification.
- [x] Module parameters. *(🟢 — depends on basic modules first.)* Implemented defs-only:
  every def in `module M (A : Type) where` is closed over the params, sibling refs
  auto-apply them, consumers instantiate by application; datatypes/records/imports and
  nesting inside parameterized modules are rejected with clear errors — see the
  implementation-log entry at the top of this file and `docs/reference.md` §13.
- [x] Module instantiation. *(🟢 — depends on module parameters.)* Implemented as
  driver-side expansion to kernel-checked definitions: `module N = M (args)` re-defines
  each member with the args applied (annotation via typechecker inference of the applied
  spine, value as a reference-spine); partial instantiation works, nested members rejected
  in v1 — see the implementation-log entry at the top of this file and
  `docs/reference.md` §13.
- [x] Qualified imports (`import M as mod`). *(🟡)* Implemented file-based in commit
  `a99fe11`: `import "f.owl" as A` forces the `A.` namespace (folding the file's own module
  segments), plain `import "f.owl"` merges names as-is; see `docs/reference.md` §13.
- [x] Selective imports (`import M only [x, y]`). *(🟢)* Implemented as visibility pruning
  over the fully-processed import (defs renamed out of the way, datatypes removed); entries
  are pre-alias dotted paths, module-prefix matching included; see the implementation-log
  entry at the top of this file and `docs/reference.md` §13.
- [x] Unification of same-name imports. *(🟢)* Implemented as provenance-based conflict
  detection: different defining files claiming one visible name → hard error; same-file
  re-merges and local shadowing allowed; `only [...]` hiding suppresses participation. See
  the implementation-log entry at the top of this file and `docs/reference.md` §13.

### E. Proof Assistant UX 🟡

- [ ] **Interactive REPL proof sessions** — per-tactic goal display (`:proof` / `:goals` / `:admit` / `:done`). *(🟡 — big quality-of-life improvement once hole/tactic infrastructure already exists.)*

### F. Performance & Metaprogramming 🟢

- [ ] **Incremental normalization**. *(🟢 — optimization, not correctness-blocking; current NbE already has sharing + memoization.)*
- [ ] **Bidirectional type checking**. *(🟡 — could simplify/streamline the existing infer/check split; worth revisiting if elaboration perf becomes an issue.)*
- [ ] **Reflection API**. *(🟢 — powerful but speculative; no immediate consumer.)*
- [ ] **Custom tactics**. *(🟢 — depends on the built-in tactic language and likely the reflection API.)*
- [ ] **Proof automation** (general). *(🟢 — umbrella goal; mostly subsumed by items in section B.)*

### G. Library & Ecosystem 🟢

Breadth-of-content work — valuable but doesn't gate the type theory or tooling itself.

- [ ] **Standard library**:
  - Data types (Nat, Int, List, Vector, etc.)
  - Algebra (groups, rings, fields, modules)
  - Order theory (posets, lattices)
  - Topology (continuous maps, homotopy)
  - Category theory (functors, natural transformations)
- [ ] **Documentation**:
  - Tutorial / Getting started guide
  - API reference
  - Example gallery
  - Comparison with other cubical systems (Agda cubical, cubicaltt)

### H. Algebraic Geometry 🔴

> Goal: make Owl handle algebraic geometry well. AG is ~95% **set-level commutative
> algebra + 1-categorical diagram chasing**; almost nothing uses the higher-categorical
> part of cubical type theory. "AG well" = (1) automatic ring/field computation,
> (2) ergonomic set truncation/quotients, (3) a commutative-algebra + scheme layer.
> Direction: **classical schemes first, homotopical/derived AG as the long tail** that
> the cubical core uniquely enables. Items B.3/B.4 (group solver, field solver) and the
> Int side of B.1 (omega) are folded in here.

- [x] **H1. Generic `by ring`** *(🔴 — the single highest-leverage feature; Coq/Lean AG is built on a ring tactic over arbitrary rings.)* Landed as a **Structured mode** in `Ring` (`Mode::Structured`), with the syntax **`by ring with C`** where `C : CommRing A add mul zero one` bundles the operations as parameters and the law/structural lemmas as fields:
  - In Structured mode, ops are recognized by **head-symbol equality** with the resolved `add`/`mul`/`zero`/`one` terms (via `nbe_eval_ctx` at the resolve-time context length) instead of Nat-eliminator normal-form shape; the Concrete mode keeps the original Nat path.
  - Numerals are built as iterated `one + …` over the abstract `one`; `numeral_add_eq`/`numeral_mul_eq`/`numeral_one_left_mul_eq` prove numeral arithmetic propositionally from the record's laws (Concrete mode still computes it definitionally over Nat).
  - The proof tree is assembled from `C`'s law projections and the kernel re-checks it (structural guard skipped) — the soundness backstop that caught two real solver bugs during development: an inverted `sym`-wrapped `mul_1_l` in `numeral_mul_eq`, and a systematic swap of the two distributive laws (`mul_add_l` distributes over `mul a (add b c)`, `mul_add_r` over `mul (add a b) c`) that the Nat path masked by definitional computation.
  - The `by` block must sit at the **top level** of the `def` — `resolve_tactics` only replaces a root `TBy` (a nested `fun … => by ring with C` panics at NbE).
  - `examples/comm_ring_demo.owl` proves `add_comm`, `mul_comm`, distributivity, associativity, `mul (add one one) x = add x x`, and `add (mul one x) zero = mul x one` over an abstract `CommRing`; guarded by `comm_ring_demo_example_checks` in the driver (64 MiB stack).
  - *Remaining: `neg`/`sub` (additive group) support is folded into H3; implicit instance search is H4 (the explicit `with C` form works without it).*
- [x] **H2. `by field`** *(🔴 — field identities with inverse reasoning; needed for residue/function fields. Builds on H1.)* Landed as **`by field with F`** for `F : Field A add mul inv zero one`, with `a ≠ 0` encoded as `Path A zero a -> Empty`:
  - *Part 0 — kernel `Empty` type*: constructor-less inductive types now parse (grammar.rs no longer errors on all-empty cons, and `parse_match_cases` accepts zero cases), so `lib/field_laws.owl` defines `def absurd : forall (A : Type), Empty -> A := fun A e => match e return A with`. Every other kernel path already handled zero cases.
  - *Part 1 — `lib/field_laws.owl`*: `Empty`, `absurd`, and a `Field` record whose law fields carry the exact names `Ring::resolve` projects (`trans, sym, cong_add_l/r, cong_mul_l/r, add_comm, add_assoc, add_0_l/r, mul_comm, mul_assoc, mul_1_l/r, mul_0_l/r, mul_add_l/r`) plus `inv_mul` (`nz a -> Path A (mul a (inv a)) one`), `inv_one`, `inv_mul_dist`, `inv_div`, `cong_inv`, `nz_one`, `nz_mul`. Ops are record parameters named `add`/`mul`/`inv`/`zero`/`one`.
  - *Part 2 — `src/cubical/field.rs`*: reifies each side of the goal to a fraction `(N, D)` with a proof `t = mul (canon N) (inv (canon D))` (denominator always a single raw monomial). Add/mul/inv cases reuse ring.rs's `decomp`/`expand`/`poly_merge`/`sum_canon`/`regroup`/`numeral_*` machinery (exposed `pub(crate)`, incl. `prod_term`). The inverse case (`reify_inv`) swaps numerator/denominator via `inv_div` and requires the numerator to be a single coefficient-1 monomial. The **final step** (`frac_eq`) proves `mul n0 (inv d0) = mul n1 (inv d1)` from the ring-proved cross-multiplication `mul n0 d1 = mul n1 d0` in 12 steps (`mul_1_r`, `inv_mul` insert, `mul_assoc` regroups, `mul_comm`, `inv_mul_dist`). **Nonzero discharge is structural** — normalize, reject `zero`, base case `one` via `nz_one`, strip canonical wrappers, decompose products with `nz_mul`, and match a context hypothesis whose type normalizes to `(Path A zero x -> Empty)`. The constructed proof is re-checked by the kernel (structural guard skipped, exactly like ring). *Scope: no `neg`/`sub`; `inv` of sums/numeral multiples is an explicit error; hypotheses must be per-atom (e.g. `hb : b ≠ 0`, `hd : d ≠ 0`).*
  - **Two subtle bugs the kernel backstop caught** (both about *stuck* local-variable terms): (1) **stale hypothesis indices** — tactic-introduced hypotheses are stored in the pre-push index frame, so `nz_hypothesis` must re-anchor each stored type with `shift(p + 1, 0, ty)` before normalizing (un-shifted, the codomain `Path zero b` normalizes to the wrong variable and never matches); (2) **denominators must be raw** — `discharge` and the law arguments structurally decompose a term, so denominators must be built with `prod_term` (not `canon_term`); where canonical and raw forms meet (`scale_frac`, `reify_inv`), explicit `ring_eq` bridges are inserted. Also fixed a systematic `cong_mul_l`/`cong_mul_r` confusion in `frac_eq`/`scale_frac` (left-append vs right-append) that left adjacent chain steps unconnected.
  - *Part 3 — plumbing*: `Tactic::Field(Option<Term>)` in `syntax/mod.rs` (+`shift_tactic`/`subst_tactic`), `show_tactic` in `pretty.rs`, `parse_tactic` (`field [with <term>]`), `"field"` in `is_tactic_keyword`, `Tactic::Field` arm in `tactics.rs` mirroring the `Ring` arm, `pub mod field;` in `mod.rs`. (The `by` block must sit at the root of the `def`, like `by ring`.)
  - *Part 4 — demo/tests*: `examples/field_demo.owl` proves `(a/b)·(c/d) = (ac)/(bd)`, `(a/b)+(c/d) = (ad+bc)/(bd)`, `(a/b)/(c/d) = (ad)/(bc)`, `inv (inv a) = a`, `inv (a·b) = inv a · inv b`, `a·inv a = one` (each with per-atom `≠ 0` hypotheses); `field_demo_example_checks` + `field_laws_lib_checks` in the driver on 64 MiB stacks. The demo re-check is slow in debug builds (~1 min for the biggest theorem per kernel pass, ~5 min total for the demo).
  - *Remaining: `neg`/`sub` (additive group) support is folded into H3.*
- [x] **H3. Int `by omega` + group solver** *(🟡)* Both halves landed: the group solver
  (see §B.3) and omega-over-Int plus a first batch of concrete integer algebra
  (additive commutativity/unit laws, double negation, multiplicative commutativity and
  unit/zero laws — see the H3 log entry at the top of this file). Deferred follow-up:
  `int_add_assoc`, `int_mul_assoc`, distributivity, and the `CommRing` record bundling that
  would route `by ring` over Int — natural groundwork for §H5.
- [x] **H4. Bundled algebra records + lightweight instance search** *(🔴 — without typeclasses, every theorem must thread `CommRing R` explicitly. Minimal implicit-argument + instance-search layer, Lean/Coq-style, on top of the existing record system.)* Done: implicit binder syntax `{x : A}` with `TPi` flag; parser, pretty-printer, typechecker auto-fill via context search; global `Env.instances` DB; tactics use context. See log entry at top.
- [ ] **Kernel perf follow-ups (profiled 2026-08, post verify-once)** *(🟡 — only if large-proof
  checking feels slow again; `OWL_TIMINGS=1` first)*. After the perf pass,
  `field_demo.owl`'s remaining ~25 s is ONE `infer_dt/check_dt` traversal of a
  ~392k-node law-application tree with ~1 G allocations. Candidate levers in
  expected order: (a) cache/memoize leaf-law type instantiation during re-check
  (each leaf application currently normalizes its instantiated Pi type fresh —
  args differ so the whole-term `eval_cache` never hits); (b) term sharing
  (`Rc<Term>`/hash-consing) for O(1) clones + pointer-eq fast paths — invasive,
  de Bruijn bug class, do behind a full-suite run; (c) shrink `infer_dt` frames.
- [ ] **H5. Commutative algebra library** *(🔴)*: `CommRing`/`Field`/`Module`/`Ideal` structures; quotient rings `R/I` and localization `S⁻¹R` via the existing HIT quotients; polynomial rings `R[X]`; prime/maximal ideals; finite fields `F_p`.
  **In progress**: structures half landed — `lib/algebra.owl` consolidates
  `CommRing`/`Group`/`Field` and adds the `Module` record (with the kernel's first
  record-typed parameter: the ring side is a bundled `CommRing` argument; see
  examples/module_demo.owl). Remaining: complete Int assoc/distributivity proofs then bundle
  `IntCommRing` (the first concrete instance, unblocking self-modules); Ideal predicates;
  R[X]; quotients/localization (relation-parameterized HITs — research-level); F_p.
  **Session-3/4 state**: `NatCommRing` — the first concrete CommRing instance — is
  bundled in lib/algebra.owl; consumers prove identities by direct field projection
  (`exact (NatCommRing.mul_comm a b)`); see examples/natcommring_demo.owl + driver guard.
  Kernel progress: `as_add`/`as_mul`/`numeral_of` now attempt RAW syntactic spine
  matching before normalization, and structured ring tactics receive the un-normalized
  goal type (Pi-stripped) so concrete heads can survive reification. Remaining before
  automatic `by ring with NatCommRing`: canonical-numeral handling in the structured
  reifier (suc-chains vs `add one (...)` canonical forms interact across
  expand/reify_add/reify_mul), plus proof-term construction for mixed concrete shapes;
  a pre-existing `-d` trace re-entrancy bug was also fixed en route (reduction_trace
  moved out of Session into nbe/trace.rs).
  (The test-time / stack-overflow iteration blocker was resolved 2026-08 — see the
  perf log entry atop this file; remaining kernel-perf ideas live in their own open item.)
  **Session-2 findings on the int assoc/distributivity blocker**: the
  truncated-subtraction encoding (`pos`/`negsuc` + `_owl_add_pos_neg`) is itself the
  obstacle. Four one-directional APN bridges were designed and two fully proven
  (`apn_pos_lift`, plus congruence helpers — later reverted with the experimental batch to
  keep the library at a committed-green state; derivations preserved in this note). The
  hard wall: any proof lifting `nat_add a b ↔ suc/add-form` through an APN slot needs its
  path argument evaluated inside a stuck-elim context, which this kernel suppresses — each
  workaround spawned a deeper lemma whose own instantiations hit the same wall one level
  further in. **Recommended route**: switch the library's Int to a sign/magnitude-style
  encoding (or difference-of-naturals pairs quotiented), where add/assoc/distributivity are
  plain case analyses with constructor-driven reductions; then reprove the CommRing bundle
  cheaply. The current pos/negsuc Int stays for omega's definitional tier.
- [ ] **H6. Set-level foundation polish** *(🟡)*: quotient elimination ergonomics, proof irrelevance for Prop, `isSet` stability — AG objects are all sets.
- [ ] **H7. Category + sheaf core** *(🔴)*: categories, functors, natural transformations, Yoneda; presheaves and sheaves; the Zariski site.
- [ ] **H8. Schemes** *(🔴)*: **functor-of-points route** — `Spec R := Hom(R, −)` on `CommRing^op`; a scheme is a Zariski sheaf locally represented by affines (the UniMath approach). Avoids building the structure sheaf on a point-set, which is far costlier in type theory. Targets: `Spec R`, Zariski opens `D(f)`, affine cover, products/pullbacks, projective space `P^n`, closed/open immersions.
- [ ] **H9. Long tail — derived schemes / higher stacks** *(🟢 — where cubical/HoTT genuinely shines over vanilla ITT: simplicial rings, homotopy limits/colimits, higher truncation. Research-level.)*
- [ ] **H10. Ergonomics blockers at library scale** *(🟡)*: `forall` cannot follow `->` (`docs/reference.md:213` — all binders must precede the arrow chain) and the basic module/import system (§D) become painful for a growing AG library.

---

## Suggested Order of Attack

1. 🔴 **Cumulativity for Σ/Π and records** — closes soundness gaps in an already-partial feature; cheap relative to payoff.
2. 🔴 **Omega (linear arithmetic)** — `by omega` landed (see §B.1); **Ring solver** landed (see §B.2, `by ring` over `Nat`) with the generic abstract-ring form `by ring with C` landed under H1 — the Group and Field solvers have since landed (§B.3, §B.4/H2); the remaining automation-ladder item is the Int side (§H3).
3. 🟡 **Module system basics** (`module M where`) + **qualified imports** — needed before the standard library work in §G can scale.
4. 🟡 **Nested constructor patterns** — moderate-cost ergonomics fix, independent of everything else.
5. 🟡 **Interactive REPL proof sessions** — biggest remaining UX win, builds on existing hole/tactic machinery.
6. 🟢 Remaining items (reflection API, custom tactics, incremental normalization, stdlib, docs) — valuable but can proceed in parallel/opportunistically once the above land.
7. 🔴 **Algebraic geometry** — follow §H in order: H1 (generic `by ring`) has landed (see §H.1 / §B.2); proceed with H4 (instance search) → H2 (`by field`) → H5 (comm algebra) → H7 (categories/sheaves) → H8 (schemes). H6/H10 unlock as library size grows.
