use crate::cubical::nbe::ReductionStep;
use crate::cubical::syntax::{Name, Term, nat_to_int, show_term};
use crate::cubical::interval::{I, DNF};

use std::cell::Cell;

thread_local! {
    static NODE_ID: Cell<u32> = const { Cell::new(0) };
}

fn next_id() -> u32 {
    NODE_ID.with(|id| {
        let v = id.get() + 1;
        id.set(v);
        v
    })
}

fn ast_node(kind: &str, label: &str, children: Vec<JsVal>) -> JsVal {
    JsVal::Obj(vec![
        kv("id", JsVal::Num(next_id() as i64)),
        kv("kind", JsVal::Str(kind.into())),
        kv("label", JsVal::Str(label.into())),
        kv("children", JsVal::Arr(children)),
    ])
}

// Minimal JSON value type (no external dependencies)
pub enum JsVal {
    Null,
    Bool(bool),
    Num(i64),
    Str(String),
    Arr(Vec<JsVal>),
    Obj(Vec<(String, JsVal)>),
}

impl JsVal {
    fn esc(s: &str) -> String {
        let mut out = String::with_capacity(s.len() + 2);
        out.push('"');
        for c in s.chars() {
            match c {
                '\\' => out.push_str("\\\\"),
                '"' => out.push_str("\\\""),
                '\n' => out.push_str("\\n"),
                '\r' => out.push_str("\\r"),
                '\t' => out.push_str("\\t"),
                c => out.push(c),
            }
        }
        out.push('"');
        out
    }

    pub fn to_string(&self) -> String {
        match self {
            JsVal::Null => "null".into(),
            JsVal::Bool(b) => (if *b { "true" } else { "false" }).into(),
            JsVal::Num(n) => n.to_string(),
            JsVal::Str(s) => Self::esc(s),
            JsVal::Arr(a) => {
                let items: Vec<String> = a.iter().map(|v| v.to_string()).collect();
                format!("[{}]", items.join(","))
            }
            JsVal::Obj(pairs) => {
                let items: Vec<String> = pairs
                    .iter()
                    .map(|(k, v)| format!("{}:{}", Self::esc(k), v.to_string()))
                    .collect();
                format!("{{{}}}", items.join(","))
            }
        }
    }
}

fn kv(k: &str, v: JsVal) -> (String, JsVal) {
    (k.to_string(), v)
}

fn nat_json(t: &Term) -> JsVal {
    if let Some(n) = nat_to_int(t) {
        JsVal::Obj(vec![
            kv("kind", JsVal::Str("nat".into())),
            kv("value", JsVal::Num(n)),
        ])
    } else {
        term_to_json(t)
    }
}

fn bool_json(val: bool) -> JsVal {
    JsVal::Obj(vec![
        kv("kind", JsVal::Str("bool".into())),
        kv("value", JsVal::Bool(val)),
    ])
}

fn constructor_json(data: &str, con: &str, args: &[Term]) -> JsVal {
    let elem_json: Vec<JsVal> = args.iter().map(term_to_json).collect();
    JsVal::Obj(vec![
        kv("kind", JsVal::Str("constructor".into())),
        kv("data", JsVal::Str(data.into())),
        kv("constructor", JsVal::Str(con.into())),
        kv("args", JsVal::Arr(elem_json)),
    ])
}

fn detect_cons_chain(t: &Term) -> Option<Vec<&Term>> {
    match t {
        Term::TCon(_, c, args) if c == "nil" && args.is_empty() => Some(vec![]),
        Term::TCon(_, c, args) if c == "cons" && args.len() >= 2 => {
            let head = &args[0];
            let tail = &args[1];
            detect_cons_chain(tail).map(|mut rest| {
                rest.insert(0, head);
                rest
            })
        }
        _ => None,
    }
}

pub fn term_to_ast_json(t: &Term) -> JsVal {
    match t {
        Term::TVar(i) => ast_node("Var", &format!("#{}", i), vec![]),
        Term::TApp(f, a) => ast_node("App", "(_ _)", vec![term_to_ast_json(f), term_to_ast_json(a)]),
        Term::TAbs(x, b) => ast_node("Abs", &format!("λ{}", x), vec![term_to_ast_json(b)]),
        Term::TUniv(n) => ast_node("Univ", &format!("U{}", n), vec![]),
        Term::TIntervalTy => ast_node("IntervalTy", "𝕀", vec![]),
        Term::TPi(x, a, b) => ast_node("Pi", &format!("Π({}: _). _", x), vec![
            term_to_ast_json(a),
            term_to_ast_json(b),
        ]),
        Term::TInterval(i) => ast_node("Interval", &format!("{}", i), vec![]),
        Term::TCube(c) => ast_node("Cube", &format!("{}", c), vec![]),
        Term::TPath(a, u, v) => ast_node("Path", "Path _ _ _", vec![
            term_to_ast_json(a),
            term_to_ast_json(u),
            term_to_ast_json(v),
        ]),
        Term::PLam(x, b) => ast_node("PLam", &format!("⟨{}⟩ _", x), vec![term_to_ast_json(b)]),
        Term::PApp(p, r) => ast_node("PApp", "_ @ _", vec![term_to_ast_json(p), term_to_ast_json(r)]),
        Term::THComp(a, phi, u, u0) => ast_node("HComp", "hcomp", vec![
            term_to_ast_json(a),
            term_to_ast_json(phi),
            term_to_ast_json(u),
            term_to_ast_json(u0),
        ]),
        Term::TEquiv(a, b) => ast_node("Equiv", "Equiv _ _", vec![term_to_ast_json(a), term_to_ast_json(b)]),
        Term::TMkEquiv(a, b, f, g, eta, eps) => ast_node("MkEquiv", "mkEquiv", vec![
            term_to_ast_json(a), term_to_ast_json(b), term_to_ast_json(f),
            term_to_ast_json(g), term_to_ast_json(eta), term_to_ast_json(eps),
        ]),
        Term::TEquivFwd(e, x) => ast_node("EquivFwd", "equivFwd", vec![term_to_ast_json(e), term_to_ast_json(x)]),
        Term::TUa(e) => ast_node("Ua", "ua", vec![term_to_ast_json(e)]),
        Term::TTransport(p, x) => ast_node("Transport", "transport", vec![term_to_ast_json(p), term_to_ast_json(x)]),
        Term::TGlue(a, phi, te) => ast_node("Glue", "Glue", vec![term_to_ast_json(a), term_to_ast_json(phi), term_to_ast_json(te)]),
        Term::TGlueElem(phi, t, a) => ast_node("GlueElem", "glue", vec![term_to_ast_json(phi), term_to_ast_json(t), term_to_ast_json(a)]),
        Term::TUnglue(phi, te, g) => ast_node("Unglue", "unglue", vec![term_to_ast_json(phi), term_to_ast_json(te), term_to_ast_json(g)]),
        Term::TSigma(x, a, b) => ast_node("Sigma", &format!("Σ({}: _). _", x), vec![term_to_ast_json(a), term_to_ast_json(b)]),
        Term::TPair(a, b) => ast_node("Pair", "(_, _)", vec![term_to_ast_json(a), term_to_ast_json(b)]),
        Term::TFst(p) => ast_node("Fst", "fst", vec![term_to_ast_json(p)]),
        Term::TSnd(p) => ast_node("Snd", "snd", vec![term_to_ast_json(p)]),
        Term::TData(d) => ast_node("Data", d, vec![]),
        Term::TCon(data, con, args) => {
            let children: Vec<JsVal> = args.iter().map(term_to_ast_json).collect();
            if children.is_empty() {
                ast_node("Con", con, vec![])
            } else {
                ast_node("Con", &format!("{} {}", data, con), children)
            }
        }
        Term::TPCon(_data, con, args, r) => {
            let mut children: Vec<JsVal> = args.iter().map(term_to_ast_json).collect();
            children.push(term_to_ast_json(r));
            ast_node("PCon", &format!("{}@{}", con, ""), children)
        }
        Term::TElim(motive, cases, scrut) => {
            let mut children: Vec<JsVal> = vec![term_to_ast_json(motive)];
            for case in cases {
                children.push(ast_node("Case", &case.con, vec![term_to_ast_json(&case.body)]));
            }
            children.push(term_to_ast_json(scrut));
            ast_node("Elim", "elim", children)
        }
    }
}

/// Reset the node ID counter (call before a new tree).
pub fn reset_ast_ids() {
    NODE_ID.with(|id| id.set(0));
}

/// Pretty-print an interval expression for AST labels.
#[allow(dead_code)]
fn interval_to_label(i: &I) -> String {
    match i {
        I::I0 => "0".into(),
        I::I1 => "1".into(),
        I::Var(n) => format!("i{}", n),
        I::Meet(a, b) => format!("{} ∧ {}", interval_to_label(a), interval_to_label(b)),
        I::Join(a, b) => format!("{} ∨ {}", interval_to_label(a), interval_to_label(b)),
        I::Neg(a) => format!("¬{}", interval_to_label(a)),
    }
}

/// Pretty-print a DNF face for AST labels.
#[allow(dead_code)]
fn dnf_to_label(d: &DNF) -> String {
    if d.cubes.is_empty() {
        "⊥".into()
    } else if d.cubes.len() == 1 && d.cubes.iter().next().unwrap().is_empty() {
        "⊤".into()
    } else {
        let parts: Vec<String> = d.cubes.iter().map(|cube| {
            if cube.is_empty() {
                "⊤".into()
            } else {
                let lits: Vec<String> = cube.iter().map(|l| format!("{}", l)).collect();
                format!("({})", lits.join(" ∧ "))
            }
        }).collect();
        parts.join(" ∨ ")
    }
}

pub fn term_to_json(t: &Term) -> JsVal {
    match t {
        Term::TCon(d, c, args) if d == "Nat" => match (c.as_str(), args.as_slice()) {
            ("zero", []) => nat_json(t),
            ("suc", [_]) => nat_json(t),
            _ => constructor_json(d, c, args),
        },
        Term::TCon(d, c, args)
            if d == "Bool" && c == "true" && args.is_empty() =>
        {
            bool_json(true)
        }
        Term::TCon(d, c, args)
            if d == "Bool" && c == "false" && args.is_empty() =>
        {
            bool_json(false)
        }
        Term::TPair(a, b) => JsVal::Obj(vec![
            kv("kind", JsVal::Str("pair".into())),
            kv("first", term_to_json(a)),
            kv("second", term_to_json(b)),
        ]),
        Term::TCon(d, c, args) if detect_cons_chain(t).is_some() => {
            let elems = detect_cons_chain(t).unwrap();
            JsVal::Obj(vec![
                kv("kind", JsVal::Str("array".into())),
                kv(
                    "elements",
                    JsVal::Arr(elems.iter().map(|e| term_to_json(e)).collect()),
                ),
            ])
        }
        Term::TCon(d, c, args) => constructor_json(d, c, args),
        _ => JsVal::Obj(vec![
            kv("kind", JsVal::Str("string".into())),
            kv("value", JsVal::Str(show_term(&[], t))),
        ]),
    }
}

/// Export a term as AST JSON string for visualization.
pub fn export_ast_json(t: &Term) -> String {
    reset_ast_ids();
    term_to_ast_json(t).to_string()
}

/// Export a reduction trace as a JSON array.
pub fn export_trace_json(steps: &[ReductionStep]) -> String {
    let items: Vec<String> = steps
        .iter()
        .map(|s| {
            format!(
                r#"{{"rule":{},"input":{},"output":{}}}"#,
                JsVal::Str(s.rule.clone()).to_string(),
                JsVal::Str(s.input.clone()).to_string(),
                JsVal::Str(s.output.clone()).to_string(),
            )
        })
        .collect();
    format!("[{}]", items.join(","))
}

/// Export a term with its pretty-printed text.
pub fn export_ast_json_with_text(t: &Term, global_names: &[Name]) -> String {
    reset_ast_ids();
    let text = show_term(global_names, t);
    let ast = term_to_ast_json(t);
    // Wrap the AST node with the text field
    match ast {
        JsVal::Obj(mut pairs) => {
            pairs.push(kv("text", JsVal::Str(text)));
            JsVal::Obj(pairs).to_string()
        }
        other => other.to_string(),
    }
}
