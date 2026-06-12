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

    // Deep recursion (e.g. Peano at 300 levels) needs big stacks on EVERY thread
    // that may run eval — including rayon workers, which default to 2MB and
    // continue the recursion whenever evaluation passes through a parallel
    // region. Configure the global pool before any rayon use.
    rayon::ThreadPoolBuilder::new()
        .stack_size(32 * 1024 * 1024)
        .build_global()
        .expect("failed to configure rayon thread pool");

    let builder = std::thread::Builder::new()
        .name("eval-worker".into())
        .stack_size(32 * 1024 * 1024);

    let handle = builder
        .spawn(move || -> Result<(), String> {
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

            let results = rt.load_file(&path).map_err(|e| format!("{}", e))?;
            for result in results {
                println!("{}", result.to_sexpr_string());
            }
            Ok(())
        })
        .expect("failed to spawn eval thread");

    match handle.join() {
        Ok(Ok(())) => {}
        Ok(Err(e)) => {
            eprintln!("Error: {}", e);
            std::process::exit(1);
        }
        Err(_) => {
            eprintln!("Fatal error: worker thread panicked");
            std::process::exit(1);
        }
    }
}
