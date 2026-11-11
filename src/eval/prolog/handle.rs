use std::any::Any;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
use crate::atom::Grounded;
use crate::eval::prolog::ffi::record_t;

#[derive(Debug, PartialEq, Eq, Hash)]
pub struct PrologForeign {
    pub record: record_t,
}

impl PrologForeign {
    pub fn new(record: record_t) -> Self { PrologForeign { record } }
}

impl Grounded for PrologForeign {
    fn display_metta(&self) -> String { format!("<prolog-foreign:{}>", self.record) }
    fn eq_gnd(&self, other: &dyn Grounded) -> bool {
        other.as_any().downcast_ref::<PrologForeign>() == Some(self)
    }
    fn hash_gnd(&self) -> u64 {
        let mut hasher = DefaultHasher::new();
        self.record.hash(&mut hasher);
        hasher.finish()
    }
    fn as_any(&self) -> &dyn Any { self }
}
