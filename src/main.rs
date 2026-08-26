//! Command-line interface for Owl's cubical type theory kernel.

mod cubical;

use std::io::{self, Write};
use std::path::Path;

use cubical::{RunError, check, check_str, run, run_str};

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

fn repl(session: &mut cubical::session::Session) -> Result<(), String> {
    println!("Owl cubical REPL. Enter one complete declaration per line.");
    println!("Commands: :help, :load <file>, :quit");
    let stdin = io::stdin();
    let mut input = String::new();
    let mut program = String::new();

    loop {
        print!("owl> ");
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
        match line {
            ":quit" | ":q" => return Ok(()),
            ":help" | ":h" => {
                println!("Enter declarations, or use :load <file>, :quit.");
                continue;
            }
            _ => {}
        }
        if let Some(path) = line.strip_prefix(":load ") {
            let source = std::fs::read_to_string(Path::new(path.trim()))
                .map_err(|e| format!("cannot read {}: {e}", path.trim()))?;
            let candidate = format!("{program}\n{source}");
            accept_repl_program(&mut program, candidate, session);
            continue;
        }
        let candidate = format!("{program}\n{line}");
        accept_repl_program(&mut program, candidate, session);
    }
}

fn accept_repl_program(
    program: &mut String,
    candidate: String,
    session: &mut cubical::session::Session,
) {
    if let Err(error) = check_str(&candidate, session) {
        eprintln!("{error}");
        return;
    }
    *program = candidate;
    match run_str(program, session) {
        Ok(output) => println!("{output}"),
        Err(RunError::NoEntryPoint) => println!("OK"),
        Err(error) => eprintln!("{error}"),
    }
}

fn format_run_error(error: RunError) -> String {
    error.to_string()
}
