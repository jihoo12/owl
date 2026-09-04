//! Command-line interface for Owl's cubical type theory kernel.

mod cubical;

use std::collections::HashMap;
use std::io::{self, Write};
use std::path::Path;

use cubical::{RunError, check, check_str, check_str_with_holes, run, run_str};

const USAGE: &str = "\
Owl — a small cubical type theory proof assistant

Usage:
  owl check <file>       Typecheck a source file (libraries need no `main`).
  owl eval <file>        Typecheck and normalize `main` (or the last definition).
  owl repl               Start an interactive session.
  owl <file>             Alias for `owl eval <file>`.
  owl help               Show this help.

Flags:
  --debug, -d            Enable detailed debug logging (NbE reductions, typechecking).
                         Can also be set via OWL_DEBUG=1 environment variable.

Source files may import other files with: import \"path/to/module.owl\"\n";

fn main() {
    let mut args: Vec<String> = std::env::args().skip(1).collect();

    // Check for --debug flag or OWL_DEBUG env var.
    let debug = args.iter().any(|a| a == "--debug" || a == "-d")
        || std::env::var("OWL_DEBUG").map_or(false, |v| !v.is_empty() && v != "0");

    if debug {
        cubical::debug::enable();
    }

    // Remove --debug/-d from args so they don't confuse subcommand parsing.
    args.retain(|a| a != "--debug" && a != "-d");

    let mut args_iter = args.into_iter();
    // Run the whole session on a worker thread with a large stack. The
    // kernel recurses over deep normal forms (quote/subst/infer_dt); on
    // small `ulimit -s` values those recursions overflow the default 8 MiB
    // main-thread stack. Thread stacks are lazily committed, so reserving
    // 256 MiB costs nothing until deep recursion actually touches it. The
    // driver is single-threaded and its Session is thread-local, so moving
    // everything onto one worker preserves semantics exactly.
    let worker = std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || {
            cubical::session::with_session_mut(|session| match args_iter.next().as_deref() {
                None | Some("help") | Some("--help") | Some("-h") => {
                    print!("{USAGE}");
                    Ok(())
                }
                Some("check") => file_arg(args_iter.next(), "check").and_then(|path| {
                    reject_extra(args_iter)?;
                    check(&path, session)
                        .map(|()| println!("{}: OK", path.display()))
                        .map_err(format_run_error)
                }),
                Some("eval") | Some("run") => file_arg(args_iter.next(), "eval").and_then(|path| {
                    reject_extra(args_iter)?;
                    run(&path, session)
                        .map(|output| println!("{output}"))
                        .map_err(format_run_error)
                }),
                Some("repl") => {
                    if args_iter.next().is_some() {
                        Err("`owl repl` does not accept a file argument".to_string())
                    } else {
                        repl(session)
                    }
                }
                Some(path) if !path.starts_with('-') => {
                    if args_iter.next().is_some() {
                        Err("expected a single source file; run `owl help` for usage".to_string())
                    } else {
                        run(path, session)
                            .map(|output| println!("{output}"))
                            .map_err(format_run_error)
                    }
                }
                Some(command) => Err(format!(
                    "unknown command `{command}`; run `owl help` for usage"
                )),
            })
        })
        .expect("spawn owl worker thread");
    let result = match worker.join() {
        Ok(r) => r,
        Err(panic) => {
            let msg = panic
                .downcast_ref::<&str>()
                .copied()
                .or_else(|| panic.downcast_ref::<String>().map(|s| s.as_str()))
                .unwrap_or("unknown panic");
            eprintln!("owl: internal error (panic): {msg}");
            std::process::exit(101);
        }
    };

    if debug {
        let steps = cubical::nbe::trace::drain_trace();
        if !steps.is_empty() {
            if result.is_err() {
                eprintln!(
                    "\n--- NbE reduction trace ({} steps, on error) ---",
                    steps.len()
                );
            } else {
                eprintln!("\n--- NbE reduction trace ({} steps) ---", steps.len());
            }
            for (i, step) in steps.iter().enumerate() {
                eprintln!(
                    "  [{:>3}] {} {} -> {}",
                    i + 1,
                    step.rule,
                    step.input,
                    step.output
                );
            }
            eprintln!("--- end trace ---");
        }
    }

    if let Err(message) = result {
        eprintln!("owl: {message}");
        std::process::exit(1);
    }
}

fn file_arg(arg: Option<String>, command: &str) -> Result<std::path::PathBuf, String> {
    arg.map(std::path::PathBuf::from)
        .ok_or_else(|| format!("`owl {command}` requires a source file"))
}

fn reject_extra(mut args: impl Iterator<Item = String>) -> Result<(), String> {
    if args.next().is_some() {
        Err("expected a single source file; run `owl help` for usage".to_string())
    } else {
        Ok(())
    }
}

fn format_run_error(error: RunError) -> String {
    error.to_string()
}

// ---------------------------------------------------------------------------
// F1: Interactive REPL proof sessions
// ---------------------------------------------------------------------------

/// State for an active proof session (entered when a definition has unsolved
/// holes).  The user fills holes interactively until all are solved or they
/// admit/abort.
struct ProofState {
    /// Name of the definition being proved.
    def_name: String,
    /// Raw source of the type annotation (e.g. "Nat").
    def_type: String,
    /// Raw source of the body (with `?hole` markers).
    def_body: String,
    /// Unsolved holes: `(meta_id, hole_name, expected_type_display)`.
    holes: Vec<(i32, String, String)>,
    /// Solutions accumulated so far: `hole_name -> solution_source`.
    solutions: HashMap<String, String>,
    /// All declarations that came before this one (the "prefix" of the program).
    prefix: String,
}

impl ProofState {
    /// Rebuild the full definition source by substituting solutions into the
    /// body, then re-check.  Returns Ok(()) if the definition now passes.
    fn try_finish(&self, session: &mut cubical::session::Session) -> Result<(), String> {
        let body = self.substitute_solutions();
        let source = format!(
            "{}\ndef {} : {} := {}",
            self.prefix, self.def_name, self.def_type, body
        );
        check_str(&source, session).map_err(|e| e.to_string())
    }

    /// Replace every `?hole_name` in the body with its solution (wrapped in
    /// parentheses to preserve parse structure).
    fn substitute_solutions(&self) -> String {
        let mut body = self.def_body.clone();
        for (name, sol) in &self.solutions {
            // Replace `?name` with `(solution)`.  We match the `?` followed
            // by the exact hole name, then a word boundary (non-alphanumeric,
            // non-underscore).
            let needle = format!("?{name}");
            let replacement = format!("({sol})");
            let mut result = String::with_capacity(body.len());
            let mut i = 0;
            while i < body.len() {
                if body[i..].starts_with(&needle) {
                    let after = i + needle.len();
                    let ok = after >= body.len()
                        || !body.as_bytes()[after].is_ascii_alphanumeric()
                            && body.as_bytes()[after] != b'_';
                    if ok {
                        result.push_str(&replacement);
                        i = after;
                    } else {
                        result.push(body[i..].chars().next().unwrap());
                        i += body[i..].chars().next().unwrap().len_utf8();
                    }
                } else {
                    result.push(body[i..].chars().next().unwrap());
                    i += body[i..].chars().next().unwrap().len_utf8();
                }
            }
            body = result;
        }
        body
    }
}

/// Display the current goals (unsolved holes).
fn show_goals(proof: &ProofState) {
    let remaining: Vec<_> = proof
        .holes
        .iter()
        .filter(|(_, name, _)| !proof.solutions.contains_key(name))
        .collect();
    if remaining.is_empty() {
        println!("No remaining goals.");
        return;
    }
    println!("Goals ({} remaining):", remaining.len());
    for (_, name, ty) in &remaining {
        if ty.is_empty() || ty == "<unknown>" {
            println!("  ?{name}");
        } else {
            println!("  ?{name} : {ty}");
        }
    }
}

/// Try to parse a `?name := term` hole-solving command.
/// Returns `Some((hole_name, solution))` on success.
fn parse_hole_assignment(line: &str) -> Option<(String, String)> {
    let line = line.trim();
    let rest = line.strip_prefix('?')?;
    let eq_pos = rest.find(":=")?;
    let name = rest[..eq_pos].trim_end().to_string();
    let sol = rest[eq_pos + 2..].trim_start().to_string();
    if name.is_empty() || sol.is_empty() {
        return None;
    }
    // Validate hole name is a simple identifier.
    if !name.chars().all(|c| c.is_alphanumeric() || c == '_') {
        return None;
    }
    Some((name, sol))
}

fn repl(session: &mut cubical::session::Session) -> Result<(), String> {
    println!("Owl cubical REPL. Enter one complete declaration per line.");
    println!("Commands: :help, :load <file>, :quit");
    println!(
        "Proof mode: enter a def with holes, then :goals, ?hole := term, :done, :admit, :abort"
    );
    let stdin = io::stdin();
    let mut input = String::new();
    let mut program = String::new();
    let mut proof: Option<ProofState> = None;

    loop {
        if proof.is_some() {
            print!("proof> ");
        } else {
            print!("owl> ");
        }
        io::stdout().flush().map_err(|e| e.to_string())?;
        input.clear();
        if stdin.read_line(&mut input).map_err(|e| e.to_string())? == 0 {
            println!();
            return Ok(());
        }
        let line = input.trim();
        if line.is_empty() {
            continue;
        }

        // ── proof-mode commands ──────────────────────────────────────────
        if let Some(ref mut p) = proof {
            match line {
                ":quit" | ":q" => return Ok(()),
                ":help" | ":h" => {
                    println!("Proof mode commands:");
                    println!("  :goals          Show unsolved holes");
                    println!("  ?name := term   Solve a hole");
                    println!("  :done           Finish (all holes must be solved)");
                    println!("  :admit          Accept with remaining holes as axioms");
                    println!("  :abort          Discard this definition");
                    continue;
                }
                ":goals" => {
                    show_goals(p);
                    continue;
                }
                ":done" => {
                    let remaining: Vec<_> = p
                        .holes
                        .iter()
                        .filter(|(_, name, _)| !p.solutions.contains_key(name.as_str()))
                        .collect();
                    if !remaining.is_empty() {
                        eprintln!("Cannot finish: {} hole(s) still unsolved.", remaining.len());
                        show_goals(p);
                        continue;
                    }
                    match p.try_finish(session) {
                        Ok(()) => {
                            // Re-run to print the normalized result.
                            let body = p.substitute_solutions();
                            let source = format!(
                                "{}\ndef {} : {} := {}",
                                p.prefix, p.def_name, p.def_type, body
                            );
                            match run_str(&source, session) {
                                Ok(output) => println!("{output}"),
                                Err(RunError::NoEntryPoint) => println!("OK"),
                                Err(error) => eprintln!("{error}"),
                            }
                            program = source;
                            proof = None;
                        }
                        Err(e) => {
                            eprintln!("Re-check failed: {e}");
                        }
                    }
                    continue;
                }
                ":admit" => {
                    println!("Admitted '{}' (holes remain as axioms).", p.def_name);
                    proof = None;
                    continue;
                }
                ":abort" => {
                    println!("Aborted proof of '{}'.", p.def_name);
                    proof = None;
                    continue;
                }
                _ => {}
            }

            // Try parsing a hole assignment: `?name := term`
            if let Some((hole_name, solution)) = parse_hole_assignment(line) {
                // Verify the hole exists.
                if !p.holes.iter().any(|(_, n, _)| n == &hole_name) {
                    eprintln!("No hole named '?{hole_name}' in this definition.");
                    show_goals(p);
                    continue;
                }
                // Try the substitution to make sure it parses.
                p.solutions.insert(hole_name.clone(), solution);
                match p.try_finish(session) {
                    Ok(()) => {
                        println!("Hole ?{hole_name} solved.");
                        // Definition is complete — finalize like :done.
                        let body = p.substitute_solutions();
                        let source = format!(
                            "{}\ndef {} : {} := {}",
                            p.prefix, p.def_name, p.def_type, body
                        );
                        match run_str(&source, session) {
                            Ok(output) => println!("{output}"),
                            Err(RunError::NoEntryPoint) => println!("OK"),
                            Err(error) => eprintln!("{error}"),
                        }
                        program = source;
                        proof = None;
                    }
                    Err(e) => {
                        // The solution didn't work — remove it and report.
                        p.solutions.remove(&hole_name);
                        eprintln!("Solution for ?{hole_name} rejected: {e}");
                    }
                }
                continue;
            }

            eprintln!("Unknown proof command: {line}");
            println!("Commands: :goals, ?name := term, :done, :admit, :abort");
            continue;
        }

        // ── normal REPL commands ─────────────────────────────────────────
        match line {
            ":quit" | ":q" => return Ok(()),
            ":help" | ":h" => {
                println!("Enter declarations, or use :load <file>, :quit.");
                println!("Enter a def with holes to start a proof session.");
                continue;
            }
            _ => {}
        }
        if let Some(path) = line.strip_prefix(":load ") {
            let source = std::fs::read_to_string(Path::new(path.trim()))
                .map_err(|e| format!("cannot read {}: {e}", path.trim()))?;
            let candidate = format!("{program}\n{source}");
            if let Err(error) = check_str(&candidate, session) {
                eprintln!("{error}");
                continue;
            }
            program = candidate;
            match run_str(&program, session) {
                Ok(output) => println!("{output}"),
                Err(RunError::NoEntryPoint) => println!("OK"),
                Err(error) => eprintln!("{error}"),
            }
            continue;
        }

        // Try checking the input.  If it fails with unsolved holes,
        // enter proof mode instead of just printing the error.
        let candidate = format!("{program}\n{line}");
        match check_str_with_holes(&candidate, session) {
            Ok(()) => {
                // Success — accept the definition.
                program = candidate;
                match run_str(&program, session) {
                    Ok(output) => println!("{output}"),
                    Err(RunError::NoEntryPoint) => println!("OK"),
                    Err(error) => eprintln!("{error}"),
                }
            }
            Err((_error, metas)) if !metas.is_empty() => {
                // Unsolved holes — enter proof mode.
                // Extract the definition name and type from the last line.
                let (def_name, def_type) = extract_def_header(line);
                let holes: Vec<(i32, String, String)> = metas
                    .into_iter()
                    .map(|(id, name, expected)| {
                        let display = match expected {
                            Some(ty) => {
                                let names: Vec<String> = Vec::new(); // top-level, no local names
                                format!("{}", cubical::syntax::show_term(&names, &ty))
                            }
                            None => "<unknown>".to_string(),
                        };
                        (id, name, display)
                    })
                    .collect();
                println!(
                    "Entering proof mode for '{def_name}'. {} hole(s) to fill.",
                    holes.len()
                );
                show_goals(&ProofState {
                    def_name: def_name.clone(),
                    def_type: def_type.clone(),
                    def_body: extract_def_body(line).to_string(),
                    holes: holes.clone(),
                    solutions: HashMap::new(),
                    prefix: program.clone(),
                });
                proof = Some(ProofState {
                    def_name,
                    def_type,
                    def_body: extract_def_body(line).to_string(),
                    holes,
                    solutions: HashMap::new(),
                    prefix: program.clone(),
                });
            }
            Err((error, _)) => {
                // Some other error — print it.
                eprintln!("{error}");
            }
        }
    }
}

/// Extract the definition name from a `def name : ...` or `def name := ...` line.
fn extract_def_header(line: &str) -> (String, String) {
    let line = line.trim();
    let rest = line.strip_prefix("def ").unwrap_or(line);
    // Find the name (up to ` :` or ` :=`).
    let name_end = rest.find(':').unwrap_or(rest.len());
    let name = rest[..name_end].trim().to_string();
    // Find the type annotation (between `: ` and ` :=`).
    let ty = if let Some(colon_pos) = rest.find(':') {
        let after_colon = &rest[colon_pos + 1..];
        if let Some(arr_pos) = after_colon.find(":=") {
            after_colon[..arr_pos].trim().to_string()
        } else {
            after_colon.trim().to_string()
        }
    } else {
        // No type annotation — infer it.
        "<inferred>".to_string()
    };
    (name, ty)
}

/// Extract the body from a `def name : T := body` or `def name := body` line.
fn extract_def_body(line: &str) -> &str {
    let line = line.trim();
    let rest = line.strip_prefix("def ").unwrap_or(line);
    // Skip name and optional type annotation.
    if let Some(pos) = rest.find(":=") {
        rest[pos + 2..].trim_start()
    } else {
        // No `:=` — shouldn't happen for a def, but be defensive.
        rest
    }
}
