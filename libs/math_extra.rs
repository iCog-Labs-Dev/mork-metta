// Plugin: math_extra
// Provides extra math operations for MeTTa via import-rs!
//
// Compile: automatically by mork-metta's import-rs! special form
// Contract: export metta_plugin_info, metta_plugin_call, metta_plugin_free_string

use std::ffi::{CStr, CString};

static PLUGIN_INFO: &[u8] = b"math_double=1;math_square=1\0";

#[no_mangle]
pub extern "C" fn metta_plugin_info() -> *const std::ffi::c_char {
    PLUGIN_INFO.as_ptr() as *const std::ffi::c_char
}

#[no_mangle]
pub extern "C" fn metta_plugin_call(
    name: *const std::ffi::c_char,
    args: *const std::ffi::c_char,
) -> *mut std::ffi::c_char {
    let name = match unsafe { CStr::from_ptr(name) }.to_str() {
        Ok(s) => s,
        Err(_) => return std::ptr::null_mut(),
    };
    let args_str = match unsafe { CStr::from_ptr(args) }.to_str() {
        Ok(s) => s,
        Err(_) => return std::ptr::null_mut(),
    };

    let result = match name {
        "math_double" => {
            let n: i128 = match args_str.trim().parse() {
                Ok(v) => v,
                Err(_) => return std::ptr::null_mut(),
            };
            CString::new(format!("{}", n * 2))
        }
        "math_square" => {
            let n: i128 = match args_str.trim().parse() {
                Ok(v) => v,
                Err(_) => return std::ptr::null_mut(),
            };
            CString::new(format!("{}", n * n))
        }
        _ => return std::ptr::null_mut(),
    };

    match result {
        Ok(c) => c.into_raw(),
        Err(_) => std::ptr::null_mut(),
    }
}

#[no_mangle]
pub extern "C" fn metta_plugin_free_string(ptr: *mut std::ffi::c_char) {
    if !ptr.is_null() {
        unsafe { drop(CString::from_raw(ptr)); }
    }
}
