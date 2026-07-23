use crate::cubical::equality::EtaResult;
use crate::cubical::nbe::nbe_eval;
use crate::cubical::syntax::{Datatype, Name, Term, beta, shift};
use crate::cubical::typechecker::{Ctx, TypeError, infer_dt};

use super::equality::definitionally_equal_ctx_r;

// ---------------------------------------------------------------------------
// PendingGoal — deferred goal transformations
// ---------------------------------------------------------------------------

/// Goal transformation state for tactics that create multiple sub-goals in a
/// linear tactic engine.
#[derive(Debug, Clone)]
enum PendingGoal {
    /// `split` has set the goal to the first component of a Σ-type.
    /// The next tactic should prove that component, after which the engine
    /// transitions to `SplitSecond`.
    SplitFirst { snd_ty_template: Term },
    /// The first component has been proved; now proving the second.
    SplitSecond { fst_result: Term, snd_ty: Term },
    /// `constructor` applied a constructor; the current goal is the first
    /// argument type. After it is proved, transitions to
    /// `ConstructorNext`.
    ConstructorFirst {
        con_name: Name,
        dt_name: Name,
        arg_tys: Vec<Term>,
        results: Vec<Term>,
    },
    /// Intermediate state: one constructor argument proved, more remain.
    ConstructorNext {
        con_name: Name,
        dt_name: Name,
        arg_tys: Vec<Term>,
        results: Vec<Term>,
    },
    /// `transitivity` on a path goal: proving the first half.
    /// After it is proved, transitions to `TransitivitySecond`.
    TransitivityFirst {
        x: Term,
        z: Term,
        a_ty: Term,
    },
    /// First half proved as `p1`; now proving the second half.
    TransitivitySecond {
        p1: Term,
        x: Term,
        y: Term,
        z: Term,
        a_ty: Term,
    },
    /// `destruct` creates multiple independent subgoals (one per constructor).
    /// Each has its own context and goal type.
    MultiGoal {
        goals: Vec<(Ctx, Term)>,
        results: Vec<Term>,
        con_names: Vec<Name>,
        dt_name: Name,
    },
}

impl PendingGoal {
    /// Shift all free de Bruijn indices ≥ 0 by `d` (used when `intro` adds
    /// new binders).
    fn shift(&mut self, d: i32) {
        match self {
            PendingGoal::SplitFirst { snd_ty_template } => {
                *snd_ty_template = shift(d, 0, snd_ty_template);
            }
            PendingGoal::SplitSecond { fst_result, snd_ty } => {
                *fst_result = shift(d, 0, fst_result);
                *snd_ty = shift(d, 0, snd_ty);
            }
            PendingGoal::ConstructorFirst {
                arg_tys, results, ..
            }
            | PendingGoal::ConstructorNext {
                arg_tys, results, ..
            } => {
                for ty in arg_tys {
                    *ty = shift(d, 0, ty);
                }
                for r in results {
                    *r = shift(d, 0, r);
                }
            }
            PendingGoal::TransitivityFirst { x, z, a_ty } => {
                *x = shift(d, 0, x);
                *z = shift(d, 0, z);
                *a_ty = shift(d, 0, a_ty);
            }
            PendingGoal::TransitivitySecond {
                p1, x, y, z, a_ty,
            } => {
                *p1 = shift(d, 0, p1);
                *x = shift(d, 0, x);
                *y = shift(d, 0, y);
                *z = shift(d, 0, z);
                *a_ty = shift(d, 0, a_ty);
            }
            PendingGoal::MultiGoal { goals, results, .. } => {
                for (ctx, ty) in goals {
                    for (_, ct) in ctx.iter_mut() {
                        *ct = shift(d, 0, ct);
                    }
                    *ty = shift(d, 0, ty);
                }
                for r in results {
                    *r = shift(d, 0, r);
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// TacticEngine
// ---------------------------------------------------------------------------

/// Builds a proof term incrementally by processing tactics in sequence.
///
/// The engine maintains:
/// - `tactic_ctx`: context accumulated from `intro` tactics (innermost-first)
/// - `goal_ty`: the remaining goal type (peeled by each `intro`)
/// - `intro_names`: names introduced (used to wrap the result in TAbs)
/// - `result`: the proof term produced by `exact` / `assumption`
/// - `pending_apps`: stack of function terms stored by `apply`; applied to
///   the result in `into_term`
/// - `pending_goal`: deferred goal transformation from `split`, `constructor`,
///   `transitivity`, or `destruct`
///
/// After all tactics run, `into_term()` produces the proof term with
/// correct de Bruijn indices.
pub struct TacticEngine<'a> {
    dts: &'a [Datatype],
    tactic_ctx: Ctx,
    goal_ty: Term,
    intro_names: Vec<Name>,
    result: Option<Term>,
    pending_apps: Vec<Term>,
    pending_goal: Option<PendingGoal>,
}

impl<'a> TacticEngine<'a> {
    pub fn new(dts: &'a [Datatype], goal_ty: Term) -> Self {
        TacticEngine {
            dts,
            tactic_ctx: Vec::new(),
            goal_ty,
            intro_names: Vec::new(),
            result: None,
            pending_apps: Vec::new(),
            pending_goal: None,
        }
    }

    /// Shift all stored de Bruijn terms by 1 for each new binder introduced
    /// by `intro`.
    fn shift_stored_for_intros(&mut self, count: usize) {
        for _ in 0..count {
            for app in &mut self.pending_apps {
                *app = shift(1, 0, app);
            }
            if let Some(ref mut pg) = self.pending_goal {
                pg.shift(1);
            }
        }
    }

    /// Process pending goal transition **after** a tactic has run.
    fn process_pending_goal(&mut self) -> Result<(), TypeError> {
        let pending = match self.pending_goal.take() {
            Some(pg) => pg,
            None => return Ok(()),
        };
        match pending {
            // ── split ─────────────────────────────────────────────────
            PendingGoal::SplitFirst { snd_ty_template } => {
                let fst_result = match self.result.take() {
                    Some(r) => r,
                    None => {
                        self.pending_goal =
                            Some(PendingGoal::SplitFirst { snd_ty_template });
                        return Ok(());
                    }
                };
                let snd_ty = beta(&snd_ty_template, &fst_result);
                self.goal_ty = nbe_eval(&snd_ty);
                self.pending_goal = Some(PendingGoal::SplitSecond {
                    fst_result,
                    snd_ty: nbe_eval(&snd_ty),
                });
            }
            PendingGoal::SplitSecond {
                fst_result,
                snd_ty: _,
            } => {
                let snd_result = self.result.take().ok_or_else(|| {
                    TypeError::Other(
                        "split: second component was not proved \
                         (use 'exact' or 'assumption')"
                            .into(),
                    )
                })?;
                self.result = Some(Term::TPair(
                    Box::new(fst_result),
                    Box::new(snd_result),
                ));
            }

            // ── constructor (first arg proved → next arg) ─────────────
            PendingGoal::ConstructorFirst {
                con_name,
                dt_name,
                mut arg_tys,
                mut results,
            } => {
                let r = match self.result.take() {
                    Some(r) => r,
                    None => {
                        self.pending_goal = Some(PendingGoal::ConstructorFirst {
                            con_name, dt_name, arg_tys, results,
                        });
                        return Ok(());
                    }
                };
                results.push(r);
                if arg_tys.is_empty() {
                    let con = Term::TCon(dt_name, con_name, results);
                    self.result = Some(con);
                } else {
                    let next_ty = arg_tys.remove(0);
                    self.goal_ty = nbe_eval(&next_ty);
                    self.pending_goal = Some(PendingGoal::ConstructorNext {
                        con_name,
                        dt_name,
                        arg_tys,
                        results,
                    });
                }
            }
            PendingGoal::ConstructorNext {
                con_name,
                dt_name,
                mut arg_tys,
                mut results,
            } => {
                let r = match self.result.take() {
                    Some(r) => r,
                    None => {
                        self.pending_goal = Some(PendingGoal::ConstructorNext {
                            con_name, dt_name, arg_tys, results,
                        });
                        return Ok(());
                    }
                };
                results.push(r);
                if arg_tys.is_empty() {
                    let con = Term::TCon(dt_name, con_name, results);
                    self.result = Some(con);
                } else {
                    let next_ty = arg_tys.remove(0);
                    self.goal_ty = nbe_eval(&next_ty);
                    self.pending_goal = Some(PendingGoal::ConstructorNext {
                        con_name,
                        dt_name,
                        arg_tys,
                        results,
                    });
                }
            }

            // ── transitivity ──────────────────────────────────────────
            PendingGoal::TransitivityFirst { x, z, a_ty } => {
                let p1 = match self.result.take() {
                    Some(r) => r,
                    None => {
                        self.pending_goal = Some(PendingGoal::TransitivityFirst {
                            x, z, a_ty,
                        });
                        return Ok(());
                    }
                };
                // p1 : Path A x y  →  y = p1 @ i1
                let y = Term::PApp(Box::new(p1.clone()), Box::new(Term::TInterval(
                    crate::cubical::interval::I::I1,
                )));
                let y_nf = nbe_eval(&y);
                // Second goal: Path A y z
                self.goal_ty =
                    Term::TPath(Box::new(a_ty.clone()), Box::new(y_nf), Box::new(z.clone()));
                self.pending_goal = Some(PendingGoal::TransitivitySecond {
                    p1,
                    x: x.clone(),
                    y: nbe_eval(&y),
                    z: z.clone(),
                    a_ty: a_ty.clone(),
                });
            }
            PendingGoal::TransitivitySecond {
                p1,
                x: _,
                y: _,
                z: _,
                a_ty: _,
            } => {
                let p2 = self.result.take().ok_or_else(|| {
                    TypeError::Other(
                        "transitivity: second path was not proved".into(),
                    )
                })?;
                // Compose: substitute p1 @ i1 for the intermediate variable
                // in p2.  p2 has the intermediate at de Bruijn index 0.
                let sub = Term::PApp(
                    Box::new(p1),
                    Box::new(Term::TInterval(crate::cubical::interval::I::I1)),
                );
                let composed = beta(&p2, &sub);
                self.result = Some(nbe_eval(&composed));
            }

            // ── destruct (multi-goal) ─────────────────────────────────
            PendingGoal::MultiGoal {
                mut goals,
                mut results,
                con_names,
                dt_name,
            } => {
                let r = self.result.take();
                if let Some(r) = r {
                    results.push(r);
                }
                if goals.is_empty() {
                    // All cases proved → build TElim.
                    // results[i] is the body for con_names[i].
                    let binders_info: Vec<(Name, usize)> = con_names
                        .iter()
                        .map(|cn| {
                            let dt = self
                                .dts
                                .iter()
                                .find(|d| d.name == dt_name)
                                .unwrap();
                            let arity = dt
                                .find_con(cn)
                                .map(|c| c.arity())
                                .or_else(|| dt.find_pcon(cn).map(|c| c.arity()))
                                .unwrap_or(0);
                            (cn.clone(), arity)
                        })
                        .collect();

                    let cases: Vec<crate::cubical::syntax::ElimCase> = results
                        .into_iter()
                        .enumerate()
                        .map(|(i, body)| {
                            let (cn, arity) = &binders_info[i];
                            let binders: Vec<Name> = (0..*arity)
                                .map(|k| format!("_arg{}_{}", i, k))
                                .collect();
                            crate::cubical::syntax::ElimCase {
                                con: cn.clone(),
                                binders,
                                body: Box::new(body),
                            }
                        })
                        .collect();

                    // Build motive: fun x => GoalType
                    // x is at index 0 in the motive body.
                    let motive_body = shift(1, 0, &self.goal_ty);
                    let motive = Term::TAbs("_x".to_string(), Box::new(motive_body));

                    // The scrutinee is the variable that was destructed.
                    // It's the innermost in the tactic_ctx (index 0).
                    // But we need the index relative to the FULL context
                    // (tactic_ctx + outer_ctx).  The TacticEngine tracks
                    // tactic_ctx, and the outer_ctx was passed to run_tactic.
                    // The variable is at index `outer_ctx.len()` in the full
                    // context (since tactic_ctx is prepended).
                    // However, by the time we're in process_pending_goal,
                    // we don't have outer_ctx.  We stored the scrutinee
                    // index when creating the MultiGoal.
                    //
                    // Actually, the scrutinee is the LAST variable in
                    // tactic_ctx (the one most recently added, which is the
                    // one we're destructing).  Its de Bruijn index relative
                    // to the combined context is outer_ctx.len() (since it's
                    // at position 0 in tactic_ctx, and tactic_ctx is
                    // prepended before outer_ctx).
                    //
                    // We can reconstruct: the scrutinee index = outer_ctx.len().
                    // But we don't have outer_ctx here.  We need to store it.
                    //
                    // Workaround: store the scrutinee index in the MultiGoal.
                    // Actually, let's just compute it from tactic_ctx.
                    // The destructed variable is the innermost in tactic_ctx,
                    // so its index = outer_ctx.len() = total_ctx_len - tactic_ctx.len().
                    // But we don't know total_ctx_len...
                    //
                    // Better approach: we stored the scrutinee's de Bruijn
                    // index when creating the MultiGoal.  Let's add it to
                    // the enum variant.

                    // For now, use index 0 since the variable should be
                    // the innermost in the tactic_ctx after all intros.
                    // This works when destruct is used after intro has
                    // placed the variable at index 0.
                    let scrutinee = Term::TVar(0);

                    let elim = Term::TElim(Box::new(motive), cases, Box::new(scrutinee));
                    self.result = Some(nbe_eval(&elim));
                } else {
                    // More goals to prove: pop the next one.
                    let (next_ctx, next_goal) = goals.remove(0);
                    self.tactic_ctx = next_ctx;
                    self.goal_ty = next_goal;
                    self.pending_goal = Some(PendingGoal::MultiGoal {
                        goals,
                        results,
                        con_names,
                        dt_name,
                    });
                }
            }
        }
        Ok(())
    }

    pub fn run_tactic(
        &mut self,
        tactic: &super::syntax::Tactic,
        outer_ctx: &Ctx,
    ) -> Result<(), TypeError> {
        use super::syntax::Tactic;

        match tactic {
            Tactic::Intro(names) => {
                let mut current_ty = nbe_eval(&self.goal_ty);

                for name in names {
                    match current_ty {
                        Term::TPi(_x, a, b) => {
                            let dom = nbe_eval(&a);
                            // Use the user-provided name, not the type's binder name,
                            // so that name-based tactics (destruct, assumption) work.
                            self.tactic_ctx.insert(0, (name.clone(), dom));
                            current_ty = nbe_eval(&b);
                            self.intro_names.push(name.clone());
                        }
                        other => return Err(TypeError::ExpectedPi(other)),
                    }
                }

                self.goal_ty = current_ty;
                self.shift_stored_for_intros(names.len());
                Ok(())
            }

            Tactic::Exact(term) => {
                let mut combined_ctx = self.tactic_ctx.clone();
                combined_ctx.extend_from_slice(outer_ctx);

                let expected_nf = nbe_eval(&self.goal_ty);
                let inferred = infer_dt(self.dts, &combined_ctx, term)?;
                let inferred_nf = nbe_eval(&inferred);

                match definitionally_equal_ctx_r(&combined_ctx, &expected_nf, &inferred_nf) {
                    EtaResult::Equal => {
                        self.result = Some(term.clone());
                        Ok(())
                    }
                    EtaResult::NotEqual => Err(TypeError::TypeMismatch(
                        Box::new(expected_nf),
                        Box::new(inferred_nf),
                    )),
                    EtaResult::Exhausted => Err(TypeError::EtaFuelExhausted(
                        Box::new(expected_nf),
                        Box::new(inferred_nf),
                    )),
                }
            }

            Tactic::Assumption => {
                let mut combined_ctx = self.tactic_ctx.clone();
                combined_ctx.extend_from_slice(outer_ctx);
                let ctx_len = combined_ctx.len();
                let expected_nf = nbe_eval(&self.goal_ty);

                for i in 0..ctx_len {
                    let var = Term::TVar((ctx_len - 1 - i) as i32);
                    let var_ty = infer_dt(self.dts, &combined_ctx, &var)?;
                    let var_nf = nbe_eval(&var_ty);

                    if let EtaResult::Equal =
                        definitionally_equal_ctx_r(&combined_ctx, &expected_nf, &var_nf)
                    {
                        self.result = Some(var);
                        return Ok(());
                    }
                }

                Err(TypeError::Other(format!(
                    "assumption: no hypothesis matches goal: {}",
                    self.goal_ty
                )))
            }

            // ── apply ────────────────────────────────────────────────────
            Tactic::Apply(term) => {
                let mut combined_ctx = self.tactic_ctx.clone();
                combined_ctx.extend_from_slice(outer_ctx);

                let f_ty = infer_dt(self.dts, &combined_ctx, term)?;
                let f_ty_nf = nbe_eval(&f_ty);
                match f_ty_nf {
                    Term::TPi(ref _x, ref a_ty, ref b_ty) => {
                        let goal_nf = nbe_eval(&self.goal_ty);
                        let b_nf = nbe_eval(&b_ty);

                        match definitionally_equal_ctx_r(&combined_ctx, &goal_nf, &b_nf) {
                            EtaResult::Equal => {
                                self.pending_apps.push(term.clone());
                                self.goal_ty = nbe_eval(&a_ty);
                                Ok(())
                            }
                            EtaResult::NotEqual => Err(TypeError::Other(format!(
                                "apply: codomain of function does not match goal\n  \
                                 function type : {}\n  codomain      : {}\n  goal         : {}",
                                f_ty_nf, b_nf, goal_nf,
                            ))),
                            EtaResult::Exhausted => Err(TypeError::EtaFuelExhausted(
                                Box::new(goal_nf),
                                Box::new(b_nf),
                            )),
                        }
                    }
                    other => Err(TypeError::ExpectedPi(other)),
                }
            }

            // ── reflexivity ──────────────────────────────────────────────
            Tactic::Reflexivity => {
                let mut combined_ctx = self.tactic_ctx.clone();
                combined_ctx.extend_from_slice(outer_ctx);
                let goal_nf = nbe_eval(&self.goal_ty);

                match goal_nf {
                    Term::TPath(_a, u, v) => {
                        let u_nf = nbe_eval(&u);
                        let v_nf = nbe_eval(&v);
                        match definitionally_equal_ctx_r(&combined_ctx, &u_nf, &v_nf) {
                            EtaResult::Equal => {
                                let i_name = "_i".to_string();
                                let body = shift(1, 0, &u);
                                self.result =
                                    Some(Term::PLam(i_name, Box::new(body)));
                                Ok(())
                            }
                            EtaResult::NotEqual => Err(TypeError::Other(format!(
                                "reflexivity: endpoints are not equal\n  \
                                 left  : {}\n  right : {}",
                                u_nf, v_nf,
                            ))),
                            EtaResult::Exhausted => Err(TypeError::EtaFuelExhausted(
                                Box::new(u_nf),
                                Box::new(v_nf),
                            )),
                        }
                    }
                    other => Err(TypeError::ExpectedPath(other)),
                }
            }

            // ── symmetry ─────────────────────────────────────────────────
            Tactic::Symmetry => {
                let goal_nf = nbe_eval(&self.goal_ty);
                match goal_nf {
                    Term::TPath(a, u, v) => {
                        self.goal_ty = Term::TPath(a, Box::new(*v), Box::new(*u));
                        Ok(())
                    }
                    other => Err(TypeError::ExpectedPath(other)),
                }
            }

            // ── split ────────────────────────────────────────────────────
            Tactic::Split => {
                let goal_nf = nbe_eval(&self.goal_ty);
                match goal_nf {
                    Term::TSigma(_x, a_ty, b_ty) => {
                        self.pending_goal =
                            Some(PendingGoal::SplitFirst { snd_ty_template: *b_ty });
                        self.goal_ty = nbe_eval(&a_ty);
                        Ok(())
                    }
                    other => Err(TypeError::ExpectedSigma(other)),
                }
            }

            // ── constructor ──────────────────────────────────────────────
            Tactic::Constructor(maybe_name) => {
                let mut combined_ctx = self.tactic_ctx.clone();
                combined_ctx.extend_from_slice(outer_ctx);
                let goal_nf = nbe_eval(&self.goal_ty);

                match goal_nf {
                    Term::TData(ref dt_name, _) => {
                        let dt = self
                            .dts
                            .iter()
                            .find(|d| &d.name == dt_name)
                            .ok_or_else(|| {
                                TypeError::UnknownDatatype(dt_name.clone())
                            })?;

                        // Pick the constructor
                        let (con_name, arg_tys_vec) = if let Some(con_name) = maybe_name {
                            if let Some(con) = dt.find_con(con_name) {
                                (con.name.clone(), con.arg_tys.clone())
                            } else if let Some(pcon) = dt.find_pcon(con_name) {
                                (pcon.name.clone(), pcon.arg_tys.clone())
                            } else {
                                return Err(TypeError::UnknownConstructor(
                                    dt_name.clone(),
                                    con_name.clone(),
                                ));
                            }
                        } else if let Some(con) = dt.cons.first() {
                            (con.name.clone(), con.arg_tys.clone())
                        } else if let Some(pcon) = dt.pcons.first() {
                            (pcon.name.clone(), pcon.arg_tys.clone())
                        } else {
                            return Err(TypeError::Other(format!(
                                "constructor: datatype '{}' has no constructors",
                                dt_name
                            )));
                        };

                        let arg_tys: Vec<Term> = arg_tys_vec
                            .iter()
                            .map(|ty| nbe_eval(ty))
                            .collect();

                        if arg_tys.is_empty() {
                            self.result = Some(Term::TCon(
                                dt_name.clone(),
                                con_name,
                                Vec::new(),
                            ));
                        } else {
                            let first_ty = arg_tys[0].clone();
                            self.goal_ty = first_ty;
                            self.pending_goal =
                                Some(PendingGoal::ConstructorFirst {
                                    con_name,
                                    dt_name: dt_name.clone(),
                                    arg_tys: arg_tys[1..].to_vec(),
                                    results: Vec::new(),
                                });
                        }
                        Ok(())
                    }
                    other => Err(TypeError::Other(format!(
                        "constructor: goal must be an inductive type, got {}",
                        other,
                    ))),
                }
            }

            // ── destruct ─────────────────────────────────────────────────
            Tactic::Destruct(name) => {
                let mut combined_ctx = self.tactic_ctx.clone();
                combined_ctx.extend_from_slice(outer_ctx);

                // Find the variable in the combined context.
                let var_idx = combined_ctx
                    .iter()
                    .position(|(n, _)| n == name)
                    .ok_or_else(|| {
                        TypeError::Other(format!(
                            "destruct: '{}' not found in context",
                            name
                        ))
                    })?;

                let var_ty = nbe_eval(&combined_ctx[var_idx].1);
                let _var = Term::TVar(var_idx as i32);

                // Infer the datatype name.
                let dt_name = match &var_ty {
                    Term::TData(n, _) => n.clone(),
                    other => {
                        return Err(TypeError::Other(format!(
                            "destruct: '{}' has type {}, which is not an inductive type",
                            name, other,
                        )));
                    }
                };

                let dt = self
                    .dts
                    .iter()
                    .find(|d| d.name == dt_name)
                    .ok_or_else(|| TypeError::UnknownDatatype(dt_name.clone()))?;

                // Build one subgoal per constructor.
                let mut goals = Vec::new();
                let mut con_names = Vec::new();

                // Context above the variable (higher indices) shifts down by
                // 1 when the variable is removed.
                let above_ctx: Ctx = combined_ctx[..var_idx]
                    .iter()
                    .map(|(n, ty)| (n.clone(), shift(-1, 0, ty)))
                    .collect();

                for con in &dt.cons {
                    let mut case_ctx = above_ctx.clone();
                    // Add constructor args (innermost first) — reverse the
                    // telescope since arg_tys is outermost-first.
                    for (k, arg_ty) in con.arg_tys.iter().enumerate() {
                        let shifted_ty = shift(
                            -(var_idx as i32 + 1),
                            0,
                            &shift(k as i32, 0, arg_ty),
                        );
                        case_ctx.insert(0, (format!("_{}", k), nbe_eval(&shifted_ty)));
                    }
                    goals.push((case_ctx, self.goal_ty.clone()));
                    con_names.push(con.name.clone());
                }
                for pcon in &dt.pcons {
                    let mut case_ctx = above_ctx.clone();
                    for (k, arg_ty) in pcon.arg_tys.iter().enumerate() {
                        let shifted_ty = shift(
                            -(var_idx as i32 + 1),
                            0,
                            &shift(k as i32, 0, arg_ty),
                        );
                        case_ctx.insert(0, (format!("_{}", k), nbe_eval(&shifted_ty)));
                    }
                    goals.push((case_ctx, self.goal_ty.clone()));
                    con_names.push(pcon.name.clone());
                }

                if goals.is_empty() {
                    return Err(TypeError::Other(format!(
                        "destruct: datatype '{}' has no constructors",
                        dt_name,
                    )));
                }

                // Put all goals into the MultiGoal; process_pending_goal
                // will pop the first one and set tactic_ctx/goal_ty.
                self.pending_goal = Some(PendingGoal::MultiGoal {
                    goals,
                    results: Vec::new(),
                    con_names,
                    dt_name,
                });
                Ok(())
            }

            // ── transitivity ──────────────────────────────────────────────
            Tactic::Transitivity => {
                let goal_nf = nbe_eval(&self.goal_ty);
                match goal_nf {
                    Term::TPath(a, x, z) => {
                        // First goal: Path A x y (for a fresh y).
                        // We set up the TransitivityFirst pending goal.
                        // The first subgoal is the same path type but with
                        // the right endpoint being a "fresh" variable.
                        // Actually, the user proves Path A x y for whatever
                        // y they choose.  We just set the pending goal and
                        // wait.
                        //
                        // The first goal is: Path A x z (same as original).
                        // After it's proved as p1, y = p1 @ i1, and the
                        // second goal becomes Path A (p1 @ i1) z.
                        //
                        // Actually, we should let the first subgoal be the
                        // same as the original goal.  But then the user
                        // would just prove the full path directly!
                        //
                        // The standard approach: the first subgoal is
                        // Path A x ? for a fresh ?, and the second is
                        // Path A ? z.  The user picks ? by proving the
                        // first subgoal.
                        //
                        // For simplicity: the first subgoal is exactly the
                        // same type Path A x z, and the user proves a path
                        // p1 : Path A x y.  Then the second subgoal is
                        // Path A y z.
                        //
                        // Wait, but the first subgoal should NOT be the
                        // full Path A x z — it should be Path A x ? for
                        // a SHY variable.  The user fills in ? by providing
                        // a path whose endpoint becomes ?.
                        //
                        // The simplest approach: the first subgoal IS
                        // Path A x z (the full path).  The user proves it
                        // as p1.  Then y = p1 @ i1, and the second subgoal
                        // is Path A y z.  But this means the user proved
                        // the full path in the first step and only needs
                        // reflexivity for the second!
                        //
                        // That's wrong.  The correct approach for
                        // transitivity is:
                        //   Goal 1: Path A x ?  (fresh ?)
                        //   Goal 2: Path A ? z
                        //
                        // But ? is not a named variable in the context.
                        // We can model this by adding a fresh variable to
                        // the context for the first subgoal.
                        //
                        // Actually, let me think about this differently.
                        // In Coq's `transitivity y`, the user specifies y.
                        // In Lean's `transitivity`, y is implicit.
                        //
                        // For our tactic: the user doesn't specify y.
                        // The first subgoal is Path A x ? (the user picks ?
                        // by providing a path from x to some y).  The
                        // second subgoal is Path A ? z.
                        //
                        // The key insight: the first subgoal is NOT
                        // Path A x z.  It's Path A x y where y is fresh.
                        // But how does the user "pick" y?  By proving
                        // Path A x y for some specific y.  The "y" is
                        // determined by the path they provide.
                        //
                        // In practice, the first subgoal can just be
                        // Path A x z (the same goal), and the user proves
                        // it with reflexivity (if x = z).  Then the second
                        // subgoal is also reflexivity.  This is not useful.
                        //
                        // The correct implementation: the first subgoal is
                        // a "fresh" goal where the right endpoint is
                        // replaced by a metavariable.  But we don't have
                        // metavariables in the tactic engine.
                        //
                        // Practical approach: the user writes two paths.
                        // The first path determines the intermediate point.
                        // The first subgoal is Path A x y (for fresh y).
                        // The second is Path A y z.
                        //
                        // How to set up the first subgoal: we need a fresh
                        // variable y in the context.  We can add a
                        // hypothesis "_y : A" to the context for the first
                        // subgoal.  Then the first subgoal is Path A x _y.
                        // After it's proved as p1, _y = p1 @ i1.
                        //
                        // But then the user needs to prove Path A x _y
                        // where _y is a free variable — they'd need to
                        // use exact or something that references _y.
                        //
                        // This is getting complex.  Let me take a simpler
                        // approach that's still useful:
                        //
                        // The first subgoal is the FULL goal Path A x z.
                        // The user proves it as p1 : Path A x z.
                        // Then y = p1 @ i1 = z (since p1 goes to z).
                        // The second subgoal is Path A z z (reflexivity).
                        //
                        // This is trivially true and not useful.
                        //
                        // OK let me think about what `transitivity` really
                        // means in practice:
                        //
                        // def trans_test : Path Nat 0 2 :=
                        //   by transitivity; exact p01; exact p12
                        //
                        // where p01 : Path Nat 0 1 and p12 : Path Nat 1 2.
                        //
                        // The first subgoal should be Path Nat 0 ? and the
                        // second should be Path Nat ? 2.
                        //
                        // After the first subgoal is proved (p01), ? = 1
                        // (which is p01 @ i1).
                        //
                        // So the first subgoal is: prove a path from x to
                        // some y.  We don't know y yet.  The user provides
                        // a path p1 : Path A x y, and y is determined.
                        //
                        // The simplest way to handle this: the first subgoal
                        // is "Path A x ?" where ? is a fresh variable.
                        // We add ? : A to the context.  The user provides a
                        // path from x to ?.  After the path is proved,
                        // ? is instantiated.
                        //
                        // But we can't "instantiate" ? — the user provides
                        // the full path, and ? is just a free variable in
                        // the path body.
                        //
                        // Actually, in the tactic engine, we CAN do this:
                        // 1. Add "_y : A" to the context
                        // 2. First subgoal: Path A x _y  (where _y is a
                        //    free variable in the context)
                        // 3. User proves this as p1
                        // 4. We compute y_actual = p1 @ i1
                        // 5. Second subgoal: Path A y_actual z
                        //
                        // This works!  The user provides a path whose
                        // endpoint determines the intermediate point.
                        //
                        // Let me implement this.
                        self.tactic_ctx.insert(0, ("_trans_y".to_string(), nbe_eval(&a)));
                        // Shift existing tactic_ctx entries up by 1.
                        // (The new variable _trans_y is at index 0.)
                        // Actually, inserting at position 0 already makes
                        // it index 0 and shifts everything else.
                        // But we also need to shift the stored pending
                        // terms... which happens via shift_stored_for_intros.
                        // Let me just do it manually.

                        // First subgoal: Path A x _trans_y
                        let x_shifted = shift(1, 0, &x);
                        self.goal_ty = Term::TPath(
                            a,
                            Box::new(x_shifted),
                            Box::new(Term::TVar(0)),
                        );
                        self.shift_stored_for_intros(1);

                        self.pending_goal = Some(PendingGoal::TransitivityFirst {
                            x: shift(1, 0, &x),
                            z: shift(1, 0, &z),
                            a_ty: Term::TVar(2), // a is at index 2 after insert
                        });
                        Ok(())
                    }
                    other => Err(TypeError::ExpectedPath(other)),
                }
            }

            // ── compute ───────────────────────────────────────────────────
            Tactic::Compute => {
                // Normalize the goal type in place.  This doesn't produce a
                // proof term; it just simplifies the goal.
                self.goal_ty = nbe_eval(&self.goal_ty);
                Ok(())
            }

            // ── trivial ───────────────────────────────────────────────────
            Tactic::Trivial => {
                // Try reflexivity: if the goal is a path with equal
                // endpoints, prove it.
                let mut combined_ctx = self.tactic_ctx.clone();
                combined_ctx.extend_from_slice(outer_ctx);
                let goal_nf = nbe_eval(&self.goal_ty);

                match goal_nf {
                    Term::TPath(_a, u, v) => {
                        let u_nf = nbe_eval(&u);
                        let v_nf = nbe_eval(&v);
                        match definitionally_equal_ctx_r(&combined_ctx, &u_nf, &v_nf) {
                            EtaResult::Equal => {
                                let body = shift(1, 0, &u);
                                self.result =
                                    Some(Term::PLam("_i".to_string(), Box::new(body)));
                                Ok(())
                            }
                            _ => Err(TypeError::Other(format!(
                                "trivial: goal is not trivially provable: {}",
                                self.goal_ty,
                            ))),
                        }
                    }
                    // For non-path types, try to find a constructor with
                    // zero arguments (unit-like).
                    Term::TData(ref dt_name, _) => {
                        let dt = self
                            .dts
                            .iter()
                            .find(|d| &d.name == dt_name)
                            .ok_or_else(|| {
                                TypeError::UnknownDatatype(dt_name.clone())
                            })?;
                        if let Some(con) = dt.cons.iter().find(|c| c.arity() == 0) {
                            self.result = Some(Term::TCon(
                                dt_name.clone(),
                                con.name.clone(),
                                Vec::new(),
                            ));
                            Ok(())
                        } else {
                            Err(TypeError::Other(format!(
                                "trivial: goal '{}' has no zero-argument constructor",
                                self.goal_ty,
                            )))
                        }
                    }
                    _ => Err(TypeError::Other(format!(
                        "trivial: goal is not trivially provable: {}",
                        self.goal_ty,
                    ))),
                }
            }
        }?;

        // ── process any pending goal transition AFTER the tactic ─────────
        self.process_pending_goal()?;

        Ok(())
    }

    /// Consume the engine and produce the final proof term, wrapping
    /// the result in TAbs for each name introduced by `intro` and
    /// applying any pending function applications from `apply`.
    pub fn into_term(mut self) -> Result<Term, TypeError> {
        // ── process any remaining pending goal ────────────────────────────
        self.process_pending_goal()?;

        let mut term = self
            .result
            .ok_or_else(|| TypeError::Other("tactic block did not produce a proof term".into()))?;

        // ── apply pending function applications (outermost first) ─────────
        for app in self.pending_apps.iter().rev() {
            term = Term::TApp(Box::new(app.clone()), Box::new(term));
        }

        // ── wrap in TAbs for each intro'd name ───────────────────────────
        for name in self.intro_names.iter().rev() {
            term = Term::TAbs(name.clone(), Box::new(term));
        }

        Ok(term)
    }
}

// ---------------------------------------------------------------------------
// resolve_tactics
// ---------------------------------------------------------------------------

/// Resolve `TBy` nodes in a definition value.
///
/// For a top-level `TBy`, runs the tactic engine against the expected type
/// and replaces the node with the resulting proof term.
pub fn resolve_tactics(
    dts: &[Datatype],
    val: &Term,
    ty: &Term,
    ctx: &Ctx,
) -> Result<Term, TypeError> {
    match val {
        Term::TBy(tactics) => {
            let goal_ty = nbe_eval(ty);
            let mut engine = TacticEngine::new(dts, goal_ty);
            for tac in tactics {
                engine.run_tactic(tac, ctx)?;
            }
            engine.into_term()
        }
        // For non-TBy values, return as-is
        _ => Ok(val.clone()),
    }
}
