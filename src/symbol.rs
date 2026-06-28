use mork_interning::{SharedMapping, SharedMappingHandle};
use std::sync::OnceLock;
use rustc_hash::FxHashMap;

static INTERNER: OnceLock<SharedMappingHandle> = OnceLock::new();

pub fn interner() -> &'static SharedMappingHandle {
    INTERNER.get_or_init(|| SharedMapping::new())
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Symbol(pub [u8; 8]);

thread_local! {
    static STR_TO_SYM: std::cell::RefCell<FxHashMap<&'static str, Symbol>> = std::cell::RefCell::new(FxHashMap::default());
    static SYM_TO_STR: std::cell::RefCell<FxHashMap<Symbol, &'static str>> = std::cell::RefCell::new(FxHashMap::default());
}

impl Symbol {
    pub fn intern(s: &str) -> Self {
        // We do a fast thread-local check first to avoid cross-thread or pathmap overhead
        let fast_check = STR_TO_SYM.with(|cache| {
            cache.borrow().get(s).copied()
        });

        if let Some(sym) = fast_check {
            return sym;
        }

        // Fallback to mork-interning
        let handle = interner();
        let permit = handle.try_aquire_permission().unwrap_or_else(|_| panic!("failed to acquire"));
        let sym = Symbol(permit.get_sym_or_insert(s.as_bytes()));
        
        // Now get the persistent string pointer from the slab
        let bytes = handle.get_bytes(sym.0).unwrap();
        let s_static: &'static str = unsafe { std::mem::transmute(std::str::from_utf8_unchecked(bytes)) };
        
        STR_TO_SYM.with(|c| c.borrow_mut().insert(s_static, sym));
        SYM_TO_STR.with(|c| c.borrow_mut().insert(sym, s_static));
        
        sym
    }
    
    #[inline(always)]
    pub fn as_str(&self) -> &'static str {
        let fast_check = SYM_TO_STR.with(|cache| {
            cache.borrow().get(self).copied()
        });

        if let Some(s) = fast_check {
            return s;
        }

        let bytes = interner().get_bytes(self.0).unwrap();
        let s_static: &'static str = unsafe { std::mem::transmute(std::str::from_utf8_unchecked(bytes)) };
        
        STR_TO_SYM.with(|c| c.borrow_mut().insert(s_static, *self));
        SYM_TO_STR.with(|c| c.borrow_mut().insert(*self, s_static));
        
        s_static
    }
}

impl std::ops::Deref for Symbol {
    type Target = str;
    fn deref(&self) -> &Self::Target {
        self.as_str()
    }
}

impl AsRef<str> for Symbol {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl std::fmt::Debug for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Sym({:?})", self.as_str())
    }
}

impl std::fmt::Display for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}
