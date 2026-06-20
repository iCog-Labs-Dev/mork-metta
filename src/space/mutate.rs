//! Atomspace mutation operations.

use crate::atom::Atom;
use crate::func::FnTable;
use crate::space::Space;
use rustc_hash::FxHashMap as HashMap;
use std::sync::{Arc, LazyLock, Mutex};

static NAMED_MUTEXES: LazyLock<Mutex<HashMap<String, Arc<Mutex<()>>>>> =
    LazyLock::new(|| Mutex::new(HashMap::default()));

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
    pub fn_effect: HashMap<String, HashMap<u8, crate::func::Effect>>,
}

/// Add an atom to a resolved space.
/// For the default space (&self), also caches user function definitions
/// so they can be found by the fast dispatch path.
pub fn add_atom(funcs: &FnTable, space_ref: &Atom, atom: &Atom) -> Result<(), String> {
    funcs.with_resolved_space(space_ref, |space| space.add_atom(atom))?;
    funcs.bump_memo_stamp();
    if matches!(space_ref, Atom::Sym(name) if name.as_ref() == "&self") {
        maybe_cache_definition_atom(atom, funcs);
        // Also store bare head atom for match premise lookup
        if let Some((head, _)) = definition_parts(atom) {
            let _ = funcs.space.write().unwrap().add_atom(head);
        }
    }
    Ok(())
}

/// Remove an atom from a resolved space.
/// For the default space (&self), also removes cached user function definitions
/// and bare head shadow atoms.
pub fn remove_atom(funcs: &FnTable, space_ref: &Atom, atom: &Atom) -> Result<bool, String> {
    let removed = funcs.with_resolved_space(space_ref, |space| space.remove_atom(atom))?;
    if removed {
        funcs.bump_memo_stamp();
    }
    if removed && matches!(space_ref, Atom::Sym(name) if name.as_ref() == "&self") {
        maybe_uncache_definition_atom(atom, funcs);
        // Only remove head shadow if no other definition with same head remains
        if let Some((head, _)) = definition_parts(atom) {
            let keep_shadow = {
                let space = funcs.space.read().unwrap();
                space.get_atoms().iter().any(|existing| match existing {
                    Atom::Expr(items) if items.len() == 3 && items[0] == Atom::sym("=") => {
                        items.get(1) == Some(head)
                    }
                    _ => false,
                })
            };
            if !keep_shadow {
                let _ = funcs.space.write().unwrap().remove_atom(head);
            }
        }
    }
    Ok(removed)
}

fn definition_parts(atom: &Atom) -> Option<(&Atom, &Atom)> {
    match atom {
        Atom::Expr(items) if items.len() == 3 && items[0] == Atom::sym("=") => {
            Some((&items[1], &items[2]))
        }
        _ => None,
    }
}

fn maybe_cache_definition_atom(atom: &Atom, funcs: &FnTable) {
    if definition_parts(atom).is_some() {
        let _ = cache_definition_atom(atom, funcs);
    }
}

fn cache_definition_atom(atom: &Atom, funcs: &FnTable) -> Result<(), String> {
    let expr = crate::parser::atom_to_expr(atom)?;
    let (name, clause) = crate::compile::compile_definition(&expr)?;
    funcs.cache_fn(&name, clause.patterns.len() as u8, clause);
    Ok(())
}

fn maybe_uncache_definition_atom(atom: &Atom, funcs: &FnTable) {
    if definition_parts(atom).is_some() {
        let _ = uncache_definition_atom(atom, funcs);
    }
}

fn uncache_definition_atom(atom: &Atom, funcs: &FnTable) -> Result<(), String> {
    let expr = crate::parser::atom_to_expr(atom)?;
    let (name, clause) = crate::compile::compile_definition(&expr)?;
    funcs.uncache_fn(&name, clause.patterns.len() as u8);
    Ok(())
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
        .read()
        .unwrap()
        .iter()
        .map(|(name, space)| (name.clone(), space.get_atoms()))
        .collect();
    let state = funcs.state.lock().unwrap().clone();
    let fn_cache = funcs.fn_cache.read().unwrap().clone();
    let fn_effect = funcs.fn_effect.read().unwrap().clone();

    TransactionSnapshot {
        self_atoms,
        named_space_atoms,
        state,
        fn_cache,
        fn_effect,
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
        fn_effect,
    } = snapshot;

    *funcs.space.write().unwrap() = rebuild_space(&self_atoms)?;

    let mut named_spaces = HashMap::default();
    for (name, atoms) in named_space_atoms {
        named_spaces.insert(name, rebuild_space(&atoms)?);
    }
    *funcs.named_spaces.write().unwrap() = named_spaces;
    *funcs.state.lock().unwrap() = state;
    *funcs.fn_cache.write().unwrap() = fn_cache;
    *funcs.fn_effect.write().unwrap() = fn_effect;
    Ok(())
}
