use crate::cubical::equality::EtaResult;
use crate::cubical::nbe::nbe_eval;
use crate::cubical::syntax::{Datatype, Name, Term};
use crate::cubical::typechecker::{Ctx, TypeError, infer_dt};

use super::equality::definitionally_equal_ctx_r;

// ---------------------------------------------------------------------------
// TacticEngine
// ---------------------------------------------------------------------------
///
/// Builds a proof term incrementally by processing tactics in sequence.
///
/// The engine maintains:
/// - `tactic_ctx`: context accumulated from `intro` tactics (innermost-first)
/// - `goal_ty`: the remaining goal type (peeled by each `intro`)
/// - `intro_names`: names introduced (used to wrap the result in TAbs)
///
/// After all tactics run, `into_term()` produces the proof term with
/// correct de Bruijn indices.
pub struct TacticEngine<'a> {
    dts: &'a [Datatype],
    tactic_ctx: Ctx,
    goal_ty: Term,
    intro_names: Vec<Name>,
    result: Option<Term>,
}

impl<'a> TacticEngine<'a> {
    pub fn new(dts: &'a [Datatype], goal_ty: Term) -> Self {
        TacticEngine {
            dts,
            tactic_ctx: Vec::new(),
            goal_ty,
            intro_names: Vec::new(),
            result: None,
        }
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
                            self.tactic_ctx
                                .insert(0, (x.clone(), dom));
                            current_ty = nbe_eval(&b);
                            self.intro_names.push(name.clone());
                        }
                        other => return Err(TypeError::ExpectedPi(other)),
                    }
                }

                self.goal_ty = current_ty;
                Ok(())
            }

            Tactic::Exact(term) => {
                // Build the combined context: outer_ctx extended with tactic_ctx
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

            Tactic::Apply(term) => {
                let mut combined_ctx = self.tactic_ctx.clone();
                combined_ctx.extend_from_slice(outer_ctx);

                let f_ty = infer_dt(self.dts, &combined_ctx, term)?;
                match nbe_eval(&f_ty) {
                    Term::TPi(_x, _a_ty, _b_ty) => {
                        // Apply creates: TApp(term, ?remaining_goal).
                        // We need to produce TApp(term, arg) where arg is
                        // determined by the remaining tactics. For now, store
                        // the partial application and let the user provide
                        // the argument via the next tactic.
                        //
                        // Simple approach: the goal becomes the codomain,
                        // and we produce TApp(term, <subgoal>).
                        // But we need to track that the result is TApp(term, <something>).
                        //
                        // For MVP, apply just modifies the goal type:
                        //   if f : A -> B and goal is B, apply f changes goal to A
                        //   and the result will be TApp(f, <proof of A>).
                        //   But this doesn't work for dependent types.
                        //
                        // Simpler: apply creates a subterm. The result is
                        // TApp(term, TVar for the new goal).
                        // We'll use the same approach as intro: create a new
                        // meta, and resolve it later.
                        //
                        // For the simplest MVP, just check that f's codomain
                        // matches the goal, and the result is TApp(f, TVar(0))
                        // where TVar(0) is a hole that subsequent tactics fill.
                        //
                        // Actually, the simplest correct approach for apply:
                        // Store the partial application, set goal to A.
                        // After all tactics, the result is TApp(f, <last_result>).
                        // But the de Bruijn indices for the argument are in the
                        // context of the goal at that point, not the outer context.
                        //
                        // For now, let's just leave apply unimplemented with a
                        // clear error. Users can use exact for MVP.
                        Err(TypeError::Other(
                            "apply is not yet implemented in the tactic engine".into(),
                        ))
                    }
                    other => Err(TypeError::ExpectedPi(other)),
                }
            }
        }
    }

    /// Consume the engine and produce the final proof term, wrapping
    /// the result in TAbs for each name introduced by `intro`.
    pub fn into_term(self) -> Result<Term, TypeError> {
        let result = self
            .result
            .ok_or_else(|| TypeError::Other("tactic block did not produce a proof term".into()))?;

        // Wrap in TAbs from innermost to outermost.
        // intro_names is in order: first intro'd = outermost.
        // De Bruijn: innermost name is at index 0.
        // So we wrap from last to first.
        let mut term = result;
        for name in self.intro_names.iter().rev() {
            // Shift all existing variables up by 1 to account for the new binder
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
