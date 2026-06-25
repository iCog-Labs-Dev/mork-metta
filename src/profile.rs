#[cfg(feature = "profile")]
mod real_impl {
    use std::cell::RefCell;
    use std::collections::HashMap;
    use std::time::{Duration, Instant};
    use rustc_hash::FxHashMap;

    static PROFILE_MEM: std::sync::OnceLock<bool> = std::sync::OnceLock::new();

    fn get_process_memory() -> usize {
        if !*PROFILE_MEM.get_or_init(|| std::env::var_os("MORK_PROFILE_MEM").is_some()) {
            return 0;
        }
        if let Ok(s) = std::fs::read_to_string("/proc/self/statm") {
            let mut parts = s.split_whitespace();
            if let Some(size_str) = parts.next() {
                if let Ok(pages) = size_str.parse::<usize>() {
                    return pages * 4096;
                }
            }
        }
        0
    }

    #[derive(Clone, Default)]
    pub struct FuncStats {
        pub calls: u64,
        pub total_time: Duration,
        pub self_time: Duration,
        pub allocated_bytes: usize,
    }

    thread_local! {
        pub static PROFILE_DATA: RefCell<FxHashMap<&'static str, FuncStats>> = RefCell::new(FxHashMap::default());
        pub static ACTIVE_STACK: RefCell<Vec<ActiveFrame>> = RefCell::new(Vec::new());
        pub static PROFILE_OVERHEAD: RefCell<Duration> = RefCell::new(Duration::ZERO);
    }

    pub struct ActiveFrame {
        pub name: &'static str,
        pub start_time: Instant,
        pub start_alloc: usize,
        pub child_duration: Duration,
        pub start_overhead: Duration,
    }

    pub struct ProfileGuard {
        name: &'static str,
    }

    impl ProfileGuard {
        pub fn new(name: &'static str) -> Self {
            let entry_time = Instant::now();
            let start_overhead = PROFILE_OVERHEAD.with(|o| *o.borrow());

            let start_alloc = get_process_memory();
            let frame = ActiveFrame {
                name,
                start_time: Instant::now(),
                start_alloc,
                child_duration: Duration::ZERO,
                start_overhead,
            };
            ACTIVE_STACK.with(|s| s.borrow_mut().push(frame));

            let overhead = entry_time.elapsed();
            PROFILE_OVERHEAD.with(|o| {
                *o.borrow_mut() += overhead;
            });
            ProfileGuard { name }
        }

        /// Create a guard for a runtime-owned function name.
        /// Interns the name via Box::leak so the key is `&'static str` for the profile map.
        pub fn new_owned(name: &str) -> Self {
            let entry_time = Instant::now();
            let start_overhead = PROFILE_OVERHEAD.with(|o| *o.borrow());

            static INTERNER: std::sync::OnceLock<std::sync::Mutex<HashMap<String, &'static str>>> =
                std::sync::OnceLock::new();
            let map = INTERNER.get_or_init(|| std::sync::Mutex::new(HashMap::new()));
            let mut map = map.lock().unwrap();
            let static_name = *map.entry(name.to_string()).or_insert_with(|| {
                Box::leak(name.to_string().into_boxed_str())
            });

            let guard = ProfileGuard::new(static_name);

            let overhead = entry_time.elapsed();
            PROFILE_OVERHEAD.with(|o| {
                *o.borrow_mut() += overhead;
            });
            guard
        }
    }

    impl Drop for ProfileGuard {
        fn drop(&mut self) {
            let drop_entry_time = Instant::now();
            if let Some(frame) = ACTIVE_STACK.with(|s| s.borrow_mut().pop()) {
                let total_elapsed = frame.start_time.elapsed();
                let current_overhead = PROFILE_OVERHEAD.with(|o| *o.borrow());
                let overhead_during_child = current_overhead.saturating_sub(frame.start_overhead);
                let actual_child_elapsed = total_elapsed.saturating_sub(overhead_during_child);

                let current_alloc = get_process_memory();
                let allocated = current_alloc.saturating_sub(frame.start_alloc);
                let self_time = actual_child_elapsed.saturating_sub(frame.child_duration);

                ACTIVE_STACK.with(|s| {
                    let mut s = s.borrow_mut();
                    if let Some(parent) = s.last_mut() {
                        parent.child_duration += actual_child_elapsed;
                    }
                });

                PROFILE_DATA.with(|d| {
                    let mut d = d.borrow_mut();
                    let stats = d.entry(self.name).or_insert(FuncStats::default());
                    stats.calls += 1;
                    stats.total_time += actual_child_elapsed;
                    stats.self_time += self_time;
                    stats.allocated_bytes += allocated;
                });
            }
            let drop_overhead = drop_entry_time.elapsed();
            PROFILE_OVERHEAD.with(|o| {
                *o.borrow_mut() += drop_overhead;
            });
        }
    }

    pub fn print_profile_summary() {
        PROFILE_DATA.with(|d| {
            let d = d.borrow();
            let mut items: Vec<(&&'static str, &FuncStats)> = d.iter().collect();
            items.sort_by_key(|(_, s)| s.self_time);
            items.reverse();

            println!("\n======================== PROFILE SUMMARY ========================");
            println!("{:<30} {:<10} {:<12} {:<12} {:<18}", "Function", "Calls", "Total Time", "Self Time", "VMem Growth (Bytes)");
            println!("{}", "-".repeat(87));
            for (name, stats) in items {
                println!(
                    "{:<30} {:<10} {:<12?} {:<12?} {:<18}",
                    name,
                    stats.calls,
                    stats.total_time,
                    stats.self_time,
                    stats.allocated_bytes
                );
            }
            let overhead = PROFILE_OVERHEAD.with(|o| *o.borrow());
            println!("{}", "-".repeat(87));
            println!("Accumulated Profiling Overhead: {:?}", overhead);
            println!("=================================================================\n");
        });
    }
}

#[cfg(feature = "profile")]
pub use real_impl::{ProfileGuard, print_profile_summary};

#[cfg(not(feature = "profile"))]
pub struct ProfileGuard;

#[cfg(not(feature = "profile"))]
impl ProfileGuard {
    #[inline(always)]
    pub fn new(_name: &'static str) -> Self {
        ProfileGuard
    }

    #[inline(always)]
    pub fn new_owned(_name: &str) -> Self {
        ProfileGuard
    }
}

#[cfg(not(feature = "profile"))]
#[inline(always)]
pub fn print_profile_summary() {
    // ponytail: no-op when profile feature is disabled
}


