use lasso::ThreadedRodeo;
use std::sync::LazyLock;

static INTERNER: LazyLock<ThreadedRodeo> = LazyLock::new(|| ThreadedRodeo::new());

#[derive(Clone, Copy)]
pub struct Symbol(pub [u8; 8], pub &'static str);

impl PartialEq for Symbol {
    #[inline(always)]
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}
impl Eq for Symbol {}

impl std::hash::Hash for Symbol {
    #[inline(always)]
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

impl Symbol {
    pub fn intern(s: &str) -> Self {
        let spur = INTERNER.get_or_intern(s);
        let s_static: &'static str = INTERNER.resolve(&spur);

        let mut id = [0u8; 8];
        let spur_val = spur.into_inner().get();
        // Pack the 32-bit spur into the 8-byte array
        id[0..4].copy_from_slice(&spur_val.to_ne_bytes());

        Symbol(id, s_static)
    }

    #[inline(always)]
    pub fn as_str(&self) -> &'static str {
        self.1
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
