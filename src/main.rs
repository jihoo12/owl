//! Command-line interface for Owl's cubical type theory kernel.

mod cubical;

use std::io::{self, Write};
use std::path::Path;

use cubical::{RunError, check, check_str, run, run_str};

const USAGE: &str = "\
Owl — a small cubical type theory proof assistant

Usage:
  owl check <file>     Typecheck a source file (libraries need no `main`).
  owl eval <file>      Typecheck and normalize `main` (or the last definition).
  owl repl             Start an interactive session.
  owl <file>           Alias for `owl eval <file>`.
  owl help             Show this help.

Source files may import other files with: import \"path/to/module.owl\"\n";

fn main() {
    let mut args = std::env::args().skip(1);
    let result = match args.next().as_deref() {
        None | Some("help") | Some("--help") | Some("-h") => {
            print!("{USAGE}");
            Ok(())
        }
        Some("check") => file_arg(args.next(), "check").and_then(|path| {
            reject_extra(args)?;
            check(&path)
                .map(|()| println!("{}: OK", path.display()))
                .map_err(format_run_error)
        }),
        Some("eval") | Some("run") => file_arg(args.next(), "eval").and_then(|path| {
            reject_extra(args)?;
            run(&path)
                .map(|output| println!("{output}"))
                .map_err(format_run_error)
        }),
        Some("repl") => {
            if args.next().is_some() {
                Err("`owl repl` does not accept a file argument".to_string())
            } else {
                repl()
            }
        }
        Some(path) if !path.starts_with('-') => {
            if args.next().is_some() {
                Err("expected a single source file; run `owl help` for usage".to_string())
            } else {
                run(path).map(|output| println!("{output}")).map_err(format_run_error)
            }
        }
        Some(command) => Err(format!("unknown command `{command}`; run `owl help` for usage")),
    };

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

fn repl() -> Result<(), String> {
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
            accept_repl_program(&mut program, candidate);
            continue;
        }
        let candidate = format!("{program}\n{line}");
        accept_repl_program(&mut program, candidate);
    }
}

fn accept_repl_program(program: &mut String, candidate: String) {
    if let Err(error) = check_str(&candidate) {
        eprintln!("{error}");
        return;
    }
    *program = candidate;
    match run_str(program) {
        Ok(output) => println!("{output}"),
        Err(RunError::NoEntryPoint) => println!("OK"),
        Err(error) => eprintln!("{error}"),
    }
}

fn format_run_error(error: RunError) -> String {
    error.to_string()
}
