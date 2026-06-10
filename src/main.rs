/// CLI entry point for `mork-metta`.
///
/// Usage:
///   cargo run -- <file.metta>                  # MorkSpace backend (default)
///   cargo run -- <file.metta> --local          # LocalSpace backend
///
/// Reads a `.metta` file, registers function definitions, evaluates runnable
/// `!(...)` expressions, and prints results.

use mork_metta::Runtime;

fn main() {
    let args: Vec<String> = std::env::args().collect();

    let use_local = args.iter().any(|a| a == "--local");
    let path = args
        .iter()
        .skip(1)
        .find(|a| !a.starts_with("--"))
        .cloned()
        .expect("usage: mork-metta [--local] <file.metta>");

    let mut rt = if use_local {
        Runtime::new()
    } else {
        #[cfg(feature = "mork")]
        {
            let space = Box::new(mork_metta::space::MorkSpace::new());
            Runtime::with_space(space)
        }
        #[cfg(not(feature = "mork"))]
        {
            eprintln!("Error: mork feature not available (falling back to LocalSpace)");
            Runtime::new()
        }
    };

    match rt.load_file(&path) {
        Ok(Some(result)) => {
            println!("{}", result.to_sexpr_string());
        }
        Ok(None) => {}
        Err(e) => {
            eprintln!("Error: {}", e);
            std::process::exit(1);
        }
    }
}
