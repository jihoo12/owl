//! Command-line interface for Owl's cubical type theory proof assistant.

use std::io::{self, Write};
use std::path::{Path, PathBuf};

use owl_frontend::{RunError, check, check_str, check_str_with_holes, run, run_str};

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
        owl_kernel::debug::enable();
    }

    // Remove --debug/-d from args so they don't confuse subcommand parsing.
    args.retain(|a| a != "--debug" && a != "-d");

    // Initialize the tactic resolver
    owl_frontend::driver::init_tactic_resolver();

    let mut args_iter = args.into_iter();
    // Run the whole session on a worker thread with a large stack.
    let worker = std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || {
            owl_kernel::session::with_session_mut(|session| match args_iter.next().as_deref() {
                None | Some("help") | Some("--help") | Some("-h") => {
                    print!("{USAGE}");
                    Ok(())
                }
                Some("check") => file_arg(args_iter.next(), "check").and_then(|path| {
                    reject_extra(args_iter)?;
                    check(&path, session)
                        .map(|_| println!("{}: OK", path.display()))
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
    if let Err(msg) = result {
        eprintln!("owl: {msg}");
        std::process::exit(1);
    }
}

fn file_arg(arg: Option<String>, cmd: &str) -> Result<PathBuf, String> {
    arg.ok_or_else(|| format!("`owl {cmd}` requires a file argument"))
        .map(PathBuf::from)
}

fn reject_extra(mut args: impl Iterator<Item = String>) -> Result<(), String> {
    if let Some(extra) = args.next() {
        Err(format!("unexpected extra argument: {extra}"))
    } else {
        Ok(())
    }
}

fn format_run_error(err: RunError) -> String {
    match err {
        RunError::Io(e) => format!("I/O error: {e}"),
        RunError::Parse(e) => format!("parse error: {e}"),
        RunError::Type(e) => format!("type error:\n{e}"),
        RunError::Import(e) => format!("import error: {e}"),
        RunError::NoEntryPoint => "no `main` definition found".to_string(),
    }
}

fn repl(session: &mut owl_kernel::session::Session) -> Result<(), String> {
    println!("Owl REPL — type `:help` for commands.");
    let mut stdin = io::stdin();
    let mut buffer = String::new();
    let mut definitions = Vec::new();

    loop {
        print!("owl> ");
        io::stdout().flush().map_err(|e| e.to_string())?;
        buffer.clear();
        let bytes_read = stdin.read_line(&mut buffer).map_err(|e| e.to_string())?;
        if bytes_read == 0 {
            // EOF
            println!();
            break;
        }
        let line = buffer.trim();
        if line.is_empty() {
            continue;
        }

        match line {
            ":help" | ":h" => {
                println!("Commands:");
                println!("  :help, :h    Show this help");
                println!("  :goals       Show current proof goals");
                println!("  :done        Finish the current proof");
                println!("  :admit       Accept the current proof with holes");
                println!("  :abort       Discard the current proof");
                println!("  :quit, :q    Exit the REPL");
                println!("  <expr>       Evaluate an expression");
            }
            ":quit" | ":q" => break,
            cmd if cmd.starts_with(":") => {
                println!("Unknown command: {cmd}");
            }
            src => {
                // Try to parse as a definition or expression
                let full_src = format!("{}\n{}", definitions.join("\n"), src);
                match check_str(&full_src, session) {
                    Ok(_) => {
                        // If it was a definition, add it to the definitions list
                        if src.contains(":=") || src.starts_with("def ") {
                            definitions.push(src.to_string());
                        }
                        println!("OK");
                    }
                    Err(e) => {
                        // Try as an expression
                        match run_str(src, session) {
                            Ok(output) => println!("{output}"),
                            Err(e2) => {
                                println!("Error: {e}");
                                println!("  or: {e2}");
                            }
                        }
                    }
                }
            }
        }
    }
    Ok(())
}
