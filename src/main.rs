/// CLI entry point for `mork-metta`.
///
/// Usage:
///   cargo run -- <file.metta>                  # MorkSpace (PathMap trie) backend
///
/// Reads a `.metta` file, registers function definitions, evaluates runnable
/// `!(...)` expressions, and prints results.
use mork_metta::Runtime;

fn main() {
    let args: Vec<String> = std::env::args().collect();

    let path = args
        .iter()
        .skip(1)
        .find(|a| !a.starts_with("--"))
        .cloned()
        .expect("usage: mork-metta <file.metta>");

    // The default CEK engine reifies the evaluation stack onto the heap, so
    // MeTTa recursion depth no longer consumes the native call stack — the 32MB
    // per-thread workaround (which zeroed ~384MB of rayon worker stacks at
    // startup, the bulk of a profiled regression) is gone. Rayon workers use
    // their 2MB default; the eval thread keeps a modest 8MB cushion only for
    // structurally deep *expressions* (e.g. eval_constrained / data lists),
    // which is bounded by source nesting, not runtime recursion.
    let builder = std::thread::Builder::new()
        .name("eval-worker".into())
        .stack_size(8 * 1024 * 1024);

    let handle = builder
        .spawn(move || -> Result<(), String> {
            let mut rt = Runtime::with_space(Box::new(mork_metta::space::MorkSpace::new()));

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
