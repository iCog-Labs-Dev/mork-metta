#[cfg(feature = "profile")]
mod real_impl {
    use std::cell::RefCell;
    use std::time::{Duration, Instant};
    use rustc_hash::FxHashMap as HashMap;

    static PROFILE_MEM: std::sync::OnceLock<bool> = std::sync::OnceLock::new();

    fn get_process_memory() -> usize {
        if !*PROFILE_MEM.get_or_init(|| std::env::var_os("MORK_PROFILE_MEM").is_some()) {
            return 0;
        }
        // Read size (first field) from /proc/self/statm which is in pages (usually 4096 bytes)
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
        pub static PROFILE_DATA: RefCell<HashMap<&'static str, FuncStats>> = RefCell::new(HashMap::default());
        pub static ACTIVE_STACK: RefCell<Vec<ActiveFrame>> = RefCell::new(Vec::new());
    }

    pub struct ActiveFrame {
        pub name: &'static str,
        pub start_time: Instant,
        pub start_alloc: usize,
        pub child_duration: Duration,
    }

    pub struct ProfileGuard {
        name: &'static str,
    }

    impl ProfileGuard {
        pub fn new(name: &'static str) -> Self {
            let start_alloc = get_process_memory();
            let frame = ActiveFrame {
                name,
                start_time: Instant::now(),
                start_alloc,
                child_duration: Duration::ZERO,
            };
            ACTIVE_STACK.with(|s| s.borrow_mut().push(frame));
            ProfileGuard { name }
        }
    }

    impl Drop for ProfileGuard {
        fn drop(&mut self) {
            if let Some(frame) = ACTIVE_STACK.with(|s| s.borrow_mut().pop()) {
                let elapsed = frame.start_time.elapsed();
                let current_alloc = get_process_memory();
                let allocated = current_alloc.saturating_sub(frame.start_alloc);
                let self_time = elapsed.saturating_sub(frame.child_duration);

                // Update parent frame
                ACTIVE_STACK.with(|s| {
                    let mut s = s.borrow_mut();
                    if let Some(parent) = s.last_mut() {
                        parent.child_duration += elapsed;
                    }
                });

                // Update stats
                PROFILE_DATA.with(|d| {
                    let mut d = d.borrow_mut();
                    let stats = d.entry(self.name).or_insert(FuncStats::default());
                    stats.calls += 1;
                    stats.total_time += elapsed;
                    stats.self_time += self_time;
                    stats.allocated_bytes += allocated;
                });
            }
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
}

#[cfg(not(feature = "profile"))]
#[inline(always)]
pub fn print_profile_summary() {}
