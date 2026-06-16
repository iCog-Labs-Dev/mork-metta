//! Atomspace mutation operations.

use crate::atom::Atom;
use crate::func::FnTable;
use crate::space::Space;
use std::collections::HashMap;
use std::sync::{Arc, LazyLock, Mutex};

static NAMED_MUTEXES: LazyLock<Mutex<HashMap<String, Arc<Mutex<()>>>>> =
    LazyLock::new(|| Mutex::new(HashMap::new()));

/// Snapshot of mutable evaluator-backed state.
pub struct TransactionSnapshot {
    /// Atoms stored in the default space.
    pub self_atoms: Vec<Atom>,
    /// Atoms stored in each named space.
    pub named_space_atoms: HashMap<String, Vec<Atom>>,
    /// Values stored in the state map.
    pub state: HashMap<String, Atom>,
    /// Cached user clause lookup results.
    pub fn_cache: HashMap<String, HashMap<u8, Vec<crate::func::Clause>>>,
    /// Cached function purity results.
    pub fn_purity: HashMap<String, HashMap<u8, bool>>,
}

/// Add an atom to a resolved space.
pub fn add_atom(funcs: &FnTable, space_ref: &Atom, atom: &Atom) -> Result<(), String> {
    funcs.with_resolved_space(space_ref, |space| space.add_atom(atom))
}

/// Remove an atom from a resolved space.
pub fn remove_atom(funcs: &FnTable, space_ref: &Atom, atom: &Atom) -> Result<bool, String> {
    funcs.with_resolved_space(space_ref, |space| space.remove_atom(atom))
}

/// Run a closure while holding a named mutex.
pub fn with_named_mutex<R>(
    name: &str,
    body: impl FnOnce() -> Result<R, String>,
) -> Result<R, String> {
    let mutex = {
        let mut map = NAMED_MUTEXES.lock().unwrap();
        Arc::clone(
            map.entry(name.to_string())
                .or_insert_with(|| Arc::new(Mutex::new(()))),
        )
    };
    let _guard = mutex.lock().unwrap();
    body()
}

/// Capture a snapshot of mutable evaluator-backed state.
pub fn snapshot_transaction_state(funcs: &FnTable) -> TransactionSnapshot {
    let self_atoms = funcs.space.read().unwrap().get_atoms();
    let named_space_atoms = funcs
        .named_spaces
        .lock()
        .unwrap()
        .iter()
        .map(|(name, space)| (name.clone(), space.get_atoms()))
        .collect();
    let state = funcs.state.lock().unwrap().clone();
    let fn_cache = funcs.fn_cache.read().unwrap().clone();
    let fn_purity = funcs.fn_purity.read().unwrap().clone();

    TransactionSnapshot {
        self_atoms,
        named_space_atoms,
        state,
        fn_cache,
        fn_purity,
    }
}

/// Restore mutable evaluator-backed state from a snapshot.
pub fn restore_transaction_state(
    snapshot: TransactionSnapshot,
    funcs: &FnTable,
) -> Result<(), String> {
    fn rebuild_space(
        atoms: &[Atom],
    ) -> Result<Box<dyn crate::space::Space + Send + Sync>, String> {
        let space = crate::space::MorkSpace::new();
        for atom in atoms {
            space.add_atom(atom)?;
        }
        Ok(Box::new(space))
    }

    let TransactionSnapshot {
        self_atoms,
        named_space_atoms,
        state,
        fn_cache,
        fn_purity,
    } = snapshot;

    *funcs.space.write().unwrap() = rebuild_space(&self_atoms)?;

    let mut named_spaces = HashMap::new();
    for (name, atoms) in named_space_atoms {
        named_spaces.insert(name, rebuild_space(&atoms)?);
    }
    *funcs.named_spaces.lock().unwrap() = named_spaces;
    *funcs.state.lock().unwrap() = state;
    *funcs.fn_cache.write().unwrap() = fn_cache;
    *funcs.fn_purity.write().unwrap() = fn_purity;
    Ok(())
}
