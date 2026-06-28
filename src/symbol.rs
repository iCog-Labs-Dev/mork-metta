use mork_interning::{SharedMapping, SharedMappingHandle};
use std::sync::OnceLock;

static INTERNER: OnceLock<SharedMappingHandle> = OnceLock::new();

pub fn interner() -> &'static SharedMappingHandle {
    INTERNER.get_or_init(|| SharedMapping::new())
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Symbol(pub [u8; 8]);

impl Symbol {
    pub fn intern(s: &str) -> Self {
        let handle = interner();
        let permit = handle.try_aquire_permission().unwrap_or_else(|_| panic!("failed to acquire"));
        Symbol(permit.get_sym_or_insert(s.as_bytes()))
    }
    
    pub fn as_str(&self) -> &'static str {
        let bytes = interner().get_bytes(self.0).unwrap();
        unsafe { std::mem::transmute(std::str::from_utf8_unchecked(bytes)) }
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
