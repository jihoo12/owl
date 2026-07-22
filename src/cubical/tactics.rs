use crate::cubical::equality::EtaResult;
use crate::cubical::nbe::nbe_eval;
use crate::cubical::syntax::{Datatype, Name, Term, beta, shift};
use crate::cubical::typechecker::{Ctx, TypeError, infer_dt};

use super::equality::definitionally_equal_ctx_r;

// ---------------------------------------------------------------------------
// PendingGoal — deferred goal transformations (used by `split`)
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
/// - `pending_goal`: deferred goal transformation from `split`
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
    /// For `SplitFirst`, we need the result from the tactic that just proved
    /// the first component.  For `SplitSecond`, we combine the result into
    /// a `TPair`.
    fn process_pending_goal(&mut self) -> Result<(), TypeError> {
        let pending = match self.pending_goal.take() {
            Some(pg) => pg,
            None => return Ok(()),
        };
        match pending {
            PendingGoal::SplitFirst { snd_ty_template } => {
                let fst_result = match self.result.take() {
                    Some(r) => r,
                    None => {
                        // Result not set yet — put the pending goal back
                        // and wait for the next tactic to produce it.
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
            PendingGoal::SplitSecond { fst_result, snd_ty: _ } => {
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
                // pending_goal is now cleared (taken above and not re-set).
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
                        Term::TPi(x, a, b) => {
                            let dom = nbe_eval(&a);
                            self.tactic_ctx.insert(0, (x.clone(), dom));
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

                        // Check that the Pi's codomain matches the goal.
                        // For non-dependent Pi this is a direct comparison.
                        // For dependent Pi (b_ty mentions x), we compare
                        // the raw codomain which has a free variable; this
                        // succeeds when the goal literally IS that codomain
                        // (the common case after `intro` has bound the
                        // relevant variable).
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
                                // Produce the constant path <i> u.
                                // The interval binder is a separate sort but
                                // occupies a de Bruijn slot, so shift u's
                                // term variables up by 1.
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
                        // Flip the goal: prove Path A v u instead.
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
        // pending_apps is in application order: [f, g, ...] means
        // f (g (... result)).  We fold from the end.
        for app in self.pending_apps.iter().rev() {
            term = Term::TApp(Box::new(app.clone()), Box::new(term));
        }

        // ── wrap in TAbs for each intro'd name ───────────────────────────
        // intro_names is outermost-first.  De Bruijn: innermost name is at
        // index 0.  So we wrap from last to first.
        //
        // No shifting is needed because the parser already resolves de Bruijn
        // indices relative to the full term_env (which includes the intro
        // names).  So TVar(0) after `intro x` already refers to x, and
        // TAbs("x", TVar(0)) is correct.  (Pending_apps from `apply` are
        // shifted at each intro via `shift_stored_for_intros`.)
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
