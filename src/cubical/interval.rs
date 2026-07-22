// Cubical Interval — Rust port of interval.hs

use std::collections::BTreeSet;
use std::fmt;

// ---------------------------------------------------------------------------
// Interval Syntax
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum I {
    I0,
    I1,
    Var(i32),
    Meet(Box<I>, Box<I>),
    Join(Box<I>, Box<I>),
    Neg(Box<I>),
}

impl fmt::Display for I {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            I::I0 => write!(f, "0"),
            I::I1 => write!(f, "1"),
            I::Var(n) => write!(f, "i{}", n),
            I::Meet(i, j) => write!(f, "({} ∧ {})", i, j),
            I::Join(i, j) => write!(f, "({} ∨ {})", i, j),
            I::Neg(i) => write!(f, "¬{}", i),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Literal {
    Pos(i32),
    NegVar(i32),
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Literal::Pos(n) => write!(f, "i{}", n),
            Literal::NegVar(n) => write!(f, "¬i{}", n),
        }
    }
}

// DNF = Disjunctive Normal Form: a set of cubes, each cube a set of literals.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[allow(clippy::upper_case_acronyms)]
pub struct DNF {
    pub cubes: BTreeSet<BTreeSet<Literal>>,
}

impl fmt::Display for DNF {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.cubes.is_empty() {
            return write!(f, "0");
        }
        // Single empty cube => top (⊤ / 1)
        if self.cubes.len() == 1 && self.cubes.iter().next().unwrap().is_empty() {
            return write!(f, "1");
        }
        let parts: Vec<String> = self.cubes.iter().map(show_cube).collect();
        write!(f, "{}", parts.join(" ∨ "))
    }
}

fn show_cube(c: &BTreeSet<Literal>) -> String {
    if c.is_empty() {
        "1".to_string()
    } else {
        let lits: Vec<String> = c.iter().map(|l| l.to_string()).collect();
        format!("({})", lits.join(" ∧ "))
    }
}

// ---------------------------------------------------------------------------
// Interval Algebra
// ---------------------------------------------------------------------------

/// Top element: a single empty cube (always true).
pub fn dnf_top() -> DNF {
    let mut cubes = BTreeSet::new();
    cubes.insert(BTreeSet::new());
    DNF { cubes }
}

/// Bottom element: no cubes (always false).
pub fn dnf_bot() -> DNF {
    DNF {
        cubes: BTreeSet::new(),
    }
}

/// Remove any cube that is a strict superset of another cube in the set
/// (absorption / redundancy elimination).
fn simplify(cubes: BTreeSet<BTreeSet<Literal>>) -> BTreeSet<BTreeSet<Literal>> {
    cubes
        .iter()
        .filter(|c| cube_consistent(c))
        .filter(|c| {
            !cubes
                .iter()
                .filter(|other| cube_consistent(other))
                .any(|other| other != *c && other.is_subset(c))
        })
        .cloned()
        .collect()
}

/// A cube is contradictory when it contains both `i` and `¬i`.
pub fn cube_consistent(cube: &BTreeSet<Literal>) -> bool {
    cube.iter().all(|lit| !cube.contains(&neg_lit(lit)))
}

/// Evaluate an interval expression to its DNF.
pub fn eval_interval(i: &I) -> DNF {
    match i {
        I::I0 => dnf_bot(),
        I::I1 => dnf_top(),
        I::Var(n) => {
            let mut inner = BTreeSet::new();
            inner.insert(Literal::Pos(*n));
            let mut cubes = BTreeSet::new();
            cubes.insert(inner);
            DNF { cubes }
        }
        I::Neg(i) => dnf_neg(&eval_interval(i)),
        I::Meet(i, j) => dnf_meet(&eval_interval(i), &eval_interval(j)),
        I::Join(i, j) => dnf_join(&eval_interval(i), &eval_interval(j)),
    }
}

/// Disjunction (join / union of cube sets).
pub fn dnf_join(a: &DNF, b: &DNF) -> DNF {
    let union: BTreeSet<_> = a.cubes.union(&b.cubes).cloned().collect();
    DNF {
        cubes: simplify(union),
    }
}

/// Conjunction (meet / pairwise union of cubes).
pub fn dnf_meet(a: &DNF, b: &DNF) -> DNF {
    let mut product = BTreeSet::new();
    for ca in &a.cubes {
        for cb in &b.cubes {
            let merged: BTreeSet<_> = ca.union(cb).cloned().collect();
            if cube_consistent(&merged) {
                product.insert(merged);
            }
        }
    }
    DNF {
        cubes: simplify(product),
    }
}

/// Negation (De Morgan / distribute negation over DNF).
pub fn dnf_neg(d: &DNF) -> DNF {
    if d.cubes.is_empty() {
        // ¬⊥ = ⊤
        return dnf_top();
    }
    // ¬(c₁ ∨ c₂ ∨ …) = ¬c₁ ∧ ¬c₂ ∧ …
    // ¬cube = join of negated literals
    let top = dnf_top();
    d.cubes.iter().fold(top, |acc, cube| {
        let neg_cube = neg_cube(cube);
        dnf_meet(&acc, &neg_cube)
    })
}

fn neg_cube(c: &BTreeSet<Literal>) -> DNF {
    let mut cubes = BTreeSet::new();
    for lit in c {
        let mut singleton = BTreeSet::new();
        singleton.insert(neg_lit(lit));
        cubes.insert(singleton);
    }
    DNF { cubes }
}

fn neg_lit(l: &Literal) -> Literal {
    match l {
        Literal::Pos(n) => Literal::NegVar(*n),
        Literal::NegVar(n) => Literal::Pos(*n),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn meet_drops_contradictory_cube() {
        let dnf = eval_interval(&I::Meet(
            Box::new(I::Var(0)),
            Box::new(I::Neg(Box::new(I::Var(0)))),
        ));

        assert_eq!(dnf, dnf_bot());
    }

    #[test]
    fn simplify_drops_inconsistent_cubes_before_absorption() {
        let mut inconsistent = BTreeSet::new();
        inconsistent.insert(Literal::Pos(0));
        inconsistent.insert(Literal::NegVar(0));

        let mut consistent = BTreeSet::new();
        consistent.insert(Literal::Pos(1));

        let dnf = dnf_join(
            &DNF {
                cubes: [inconsistent].into_iter().collect(),
            },
            &DNF {
                cubes: [consistent.clone()].into_iter().collect(),
            },
        );

        assert_eq!(dnf.cubes, [consistent].into_iter().collect());
    }
}