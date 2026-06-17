# Universal C Library Wrapper System for PeTTa

## Your Vision → Implementation ✓

**Goal:** Create 100+ MeTTa libraries from C libraries with **zero additional C code**.

### What You Built

#### 1. **FFI Core Layer** (`ffi_core.c` + `ffi_core.so`)
- **One-time C code** (~100 lines)
- Implements 3 Prolog predicates:
  - `dlopen/2` — load C library
  - `dlsym/3` — get function pointer
  - `call_c_double/3` — call C function (returns double)
- Compiled once: `gcc ... -o ffi_core.so`

#### 2. **Prolog Wrapper** (`lib_c_wrapper_init.pl`)
- Loads `ffi_core.so` at initialization
- Wraps the 3 FFI predicates into Prolog predicates
- Manages library handles
- **No user code needed here**

#### 3. **MeTTa Export Layer** (`lib_c_wrapper.metta`)
- Imports the Prolog predicates
- Exposes them as callable MeTTa functions:
  - `!(wrap_c_lib /path/to/lib.so.6)` — load library
  - `!(c_call funcname (arg1 arg2))` — call function

## How to Create New C Library Wrappers

### Template: `lib_mylib_c.metta`

```metta
!(import! &self (library lib_c_wrapper))

; Load the C library (one-time setup at file load)
!(wrap_c_lib /path/to/libmylib.so.6)

; Define convenience functions
(= (my-func $x)
   (c_call my_c_function ($x)))

(= (my-other-func $x $y)
   (c_call my_other_c_function ($x $y)))
```

**That's it.** No Prolog. No C. Pure MeTTa.

## Working Examples

### Math Library
```metta
!(import! &self (library lib_math_c))

!(c-sqrt 16.0)      ; → 4.0
!(c-pow 2.0 3.0)    ; → 8.0
!(c-exp 1.0)        ; → 2.718...
```

### Direct C Function Calls
```metta
!(import! &self (library lib_c_wrapper))
!(wrap_c_lib /usr/lib/x86_64-linux-gnu/libm.so.6)

!(c_call sqrt (16.0))    ; → 4.0
!(c_call sin (1.57))     ; → 1.0
```

## Current Limitations & Extensions

### Supported Now
- Functions with 0-2 double-precision arguments
- Return values as doubles
- Any C library with functions matching this signature

### To Extend
For other function signatures (int args, structs, etc.), add variants:
- `call_c_int/3` — returns int
- `call_c_long/3` — returns long
- `call_c_void/3` — no return value

Each variant is a small C function (~10 lines) + update `install_ffi_core()`.

## File Structure

```
lib/
  ffi_core.c                    # Core FFI (write once)
  ffi_core.so                   # Compiled (build once)
  lib_c_wrapper_init.pl         # Prolog wrapper (write once)
  lib_c_wrapper.metta           # MeTTa export (done)
  lib_math_c.metta              # Example: math library wrapper
  lib_string_c.metta            # Example: string library wrapper
  example_c_wrapper_usage.metta # Usage examples
```

## Workflow Summary

1. ✅ **Once:** Write `ffi_core.c`, compile to `.so`
2. ✅ **Once:** Write `lib_c_wrapper_init.pl` and `lib_c_wrapper.metta`
3. 🔁 **Per library:** Create `lib_LIBNAME_c.metta` with:
   - Import lib_c_wrapper
   - Load library path
   - Define convenience functions
4. 🚀 **Use:** `!(import! &self (library lib_LIBNAME_c))`

## Result

**Zero C code for each new library.** Pure MeTTa wrapper definitions.

Create 100+ C library bindings with the effort of creating 100 pure MeTTa files.
