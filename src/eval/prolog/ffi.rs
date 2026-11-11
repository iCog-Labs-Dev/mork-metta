use std::env;
use std::ffi::{CString, c_char, c_int, c_uint, c_void};
use std::path::Path;
use std::process::Command;
use std::ptr;
use std::sync::OnceLock;
use dlopen2::wrapper::{Container, WrapperApi};
use crate::eval::prolog::error::PrologError;
#[allow(non_camel_case_types)]
pub type PL_engine_t = usize; pub type fid_t = usize; pub type term_t = usize; pub type atom_t = usize; pub type functor_t = usize;
#[allow(non_camel_case_types)]
pub type module_t = usize; pub type predicate_t = usize; pub type record_t = usize; pub type qid_t = usize;
pub const PL_ENGINE_MAIN: PL_engine_t = 1;
pub const PL_ENGINE_NONE: PL_engine_t = 0;
pub const PL_Q_NORMAL: c_int = 0x0002; pub const PL_Q_NODEBUG: c_int = 0x0004;
pub const PL_Q_CATCH_EXCEPTION: c_int = 0x0008; pub const PL_Q_EXT_STATUS: c_int = 0x0040;
pub const PL_S_TRUE: c_int = 1; pub const PL_S_LAST: c_int = 2; pub const PL_S_EXCEPTION: c_int = -1;
pub const PL_VARIABLE: c_int = 1; pub const PL_ATOM: c_int = 2; pub const PL_INTEGER: c_int = 3;
pub const PL_FLOAT: c_int = 5; pub const PL_STRING: c_int = 6; pub const PL_TERM: c_int = 7;
pub const PL_NIL: c_int = 8; pub const PL_LIST_PAIR: c_int = 10;
pub const CVT_ATOM: c_uint = 0x0001; pub const CVT_STRING: c_uint = 0x0002;
pub const CVT_INTEGER: c_uint = 0x0008; pub const CVT_WRITE: c_uint = 0x0080;
macro_rules! swipl {
    ($( $name:ident = $sym:literal ( $($arg:ident : $ty:ty),* ) -> $ret:ty; )*) => {
        #[derive(WrapperApi)]
        pub struct Api {
            $( #[dlopen2_name = $sym] $name: unsafe extern "C" fn($($arg: $ty),*) -> $ret, )*
        }
    };
}
swipl! {
    initialise = "PL_initialise"(argc: c_int, argv: *mut *mut c_char) -> c_int; create_engine = "PL_create_engine"(attr: *mut c_void) -> PL_engine_t;
    destroy_engine = "PL_destroy_engine"(engine: PL_engine_t) -> c_int; set_engine = "PL_set_engine"(engine: PL_engine_t, old: *mut PL_engine_t) -> c_int;
    open_foreign_frame = "PL_open_foreign_frame"() -> fid_t; discard_foreign_frame = "PL_discard_foreign_frame"(fid: fid_t) -> ();
    clear_exception = "PL_clear_exception"() -> (); new_term_ref = "PL_new_term_ref"() -> term_t;
    new_term_refs = "PL_new_term_refs"(n: c_int) -> term_t; put_atom = "PL_put_atom"(t: term_t, a: atom_t) -> c_int;
    put_atom_chars = "PL_put_atom_chars"(t: term_t, s: *const c_char) -> c_int; put_string_chars = "PL_put_string_chars"(t: term_t, s: *const c_char) -> c_int;
    put_int64 = "PL_put_int64"(t: term_t, v: i64) -> c_int; put_float = "PL_put_float"(t: term_t, v: f64) -> c_int;
    put_nil = "PL_put_nil"(t: term_t) -> c_int; put_variable = "PL_put_variable"(t: term_t) -> c_int;
    put_term = "PL_put_term"(t: term_t, from: term_t) -> c_int; get_chars = "PL_get_chars"(t: term_t, s: *mut *const c_char, flags: c_uint) -> c_int;
    get_int64 = "PL_get_int64"(t: term_t, v: *mut i64) -> c_int; get_float = "PL_get_float"(t: term_t, v: *mut f64) -> c_int;
    get_arg = "PL_get_arg"(index: c_int, t: term_t, a: term_t) -> c_int; get_name_arity = "PL_get_name_arity"(t: term_t, name: *mut atom_t, arity: *mut c_int) -> c_int;
    get_list = "PL_get_list"(t: term_t, head: term_t, tail: term_t) -> c_int; new_functor = "PL_new_functor"(a: atom_t, arity: c_int) -> functor_t;
    new_functor_sz = "PL_new_functor_sz"(a: atom_t, arity: usize) -> functor_t; new_atom = "PL_new_atom"(s: *const c_char) -> atom_t;
    atom_chars = "PL_atom_chars"(a: atom_t) -> *const c_char; predicate = "PL_predicate"(name: *const c_char, arity: c_int, module: *const c_char) -> predicate_t;
    new_module = "PL_new_module"(name: atom_t) -> module_t; open_query = "PL_open_query"(module: module_t, flags: c_int, pred: predicate_t, args: term_t) -> qid_t;
    call_predicate = "PL_call_predicate"(module: module_t, flags: c_int, pred: predicate_t, args: term_t) -> c_int;
    next_solution = "PL_next_solution"(qid: qid_t) -> c_int;
    close_query = "PL_close_query"(qid: qid_t) -> c_int; record = "PL_record"(t: term_t) -> record_t;
    recorded = "PL_recorded"(r: record_t, t: term_t) -> c_int; exception = "PL_exception"(qid: qid_t) -> term_t;
    chars_to_term = "PL_chars_to_term"(s: *const c_char, t: term_t) -> c_int; call = "PL_call"(t: term_t, module: module_t) -> c_int;
    term_type = "PL_term_type"(t: term_t) -> c_int; cons_functor_v = "PL_cons_functor_v"(t: term_t, f: functor_t, args: term_t) -> c_int;
    cons_list = "PL_cons_list"(t: term_t, head: term_t, tail: term_t) -> c_int;
}
static CONTAINER: OnceLock<Result<Container<Api>, PrologError>> = OnceLock::new();
impl Api {
    pub fn get() -> Result<&'static Api, PrologError> {
        CONTAINER.get_or_init(Self::load).as_ref().map(|c| &**c).map_err(Clone::clone)
    }
    fn load() -> Result<Container<Api>, PrologError> {
        unsafe {
            if let Ok(base) = env::var("PLBASE") { env::set_var("SWI_HOME_DIR", &base); }
            let path = Self::locate_library()?;
            let container: Container<Api> = Container::load(&path)
                .map_err(|e| PrologError::LibraryNotFound(format!("failed to load '{path}': {e}")))?;
            let mut argv: Vec<*mut c_char> = ["swipl", "-q", "--nosignals"].iter().map(|a| CString::new(*a).unwrap().into_raw()).collect();
            if let Ok(home) = env::var("SWI_HOME_DIR") {
                argv.push(CString::new(format!("--home={home}")).unwrap().into_raw());
            }
            argv.push(ptr::null_mut());
            let argc = (argv.len() - 1) as c_int;
            let res = container.initialise(argc, argv.as_ptr() as *mut *mut c_char);
            for ptr in argv.into_iter().take_while(|p| !p.is_null()) {
                drop(CString::from_raw(ptr));
            }
            if res == 0 {
                return Err(PrologError::InitFailed("PL_initialise returned FALSE".into()));
            }
            container.set_engine(PL_ENGINE_NONE, ptr::null_mut());
            Ok(container)
        }
    }
    fn names() -> &'static [&'static str] {
        &["libswipl.so.10", "libswipl.so.9", "libswipl.so.8", "libswipl.so", "libswipl.dylib"]
    }
    fn locate_library() -> Result<String, PrologError> {
        if let Ok(path) = env::var("MORK_METTA_LIBSWIPL") {
            if let Some(base) = Path::new(&path).parent().and_then(Path::parent).and_then(Path::parent) {
                unsafe { env::set_var("PLBASE", base) };
            }
            return Ok(path);
        }
        let home_bin = env::var("HOME").map(|h| format!("{h}/.local/bin/swipl")).unwrap_or_default();
        for swipl_bin in ["swipl", &home_bin, "/usr/bin/swipl", "/usr/local/bin/swipl"] {
            let Ok(output) = Command::new(swipl_bin).arg("--dump-runtime-variables").output()
            else { continue };
            if !output.status.success() { continue; }
            let stdout = String::from_utf8_lossy(&output.stdout);
            let var = |key: &str| stdout.lines().find_map(|l| {
                l.trim().strip_prefix(key).map(|v| v.trim_matches(|c| c == '"' || c == ';' || c == '\'').trim().to_string())
            });
            if let Some(base) = var("PLBASE=") {
                unsafe { env::set_var("SWI_HOME_DIR", &base); env::set_var("PLBASE", &base); }
            }
            if let Some(lib) = var("PLLIBSWIPL=") { return Ok(lib); }
            if let Some(dir) = var("PLLIBDIR=") {
                let cands = Self::names().iter().map(|n| format!("{dir}/{n}"));
                return Self::first_existing(cands).ok_or_else(|| PrologError::LibraryNotFound(format!("could not locate libswipl in {dir}")));
            }
        }
        let cands = Self::names().iter().map(|n| n.to_string());
        Self::first_existing(cands).ok_or_else(|| PrologError::LibraryNotFound(
            "could not locate libswipl (tried MORK_METTA_LIBSWIPL, swipl --dump-runtime-variables, and common shared library names)".into(),
        ))
    }
    fn first_existing<I: Iterator<Item = String>>(candidates: I) -> Option<String> {
        let mut bare = None;
        for cand in candidates {
            if Path::new(&cand).is_file() { return Some(cand); }
            if !cand.contains('/') { bare = Some(cand); }
        }
        bare
    }
}
