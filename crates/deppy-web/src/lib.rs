//! Small C ABI for calling the DepPy checker from a browser without a server.

use deppy_python::{analyze_module_with_options, FrontendOptions};

/// Allocate a byte buffer. The caller must release it with `release`.
#[no_mangle]
pub extern "C" fn allocate(len: u32) -> *mut u8 {
    let bytes = vec![0_u8; len as usize].into_boxed_slice();
    Box::into_raw(bytes) as *mut u8
}

/// Release a buffer returned by `allocate` or `check`.
///
/// # Safety
///
/// `ptr` must be a pointer returned by `allocate` or unpacked from `check`,
/// and `len` must be the length associated with that allocation. The buffer
/// must not have been released already or be used after this call.
#[no_mangle]
pub unsafe extern "C" fn release(ptr: *mut u8, len: u32) {
    if !ptr.is_null() {
        drop(Box::from_raw(std::ptr::slice_from_raw_parts_mut(
            ptr,
            len as usize,
        )));
    }
}

/// Return `(length << 32) | pointer` for a JSON result buffer.
/// Input stays owned by the caller and must be released separately.
///
/// # Safety
///
/// `ptr` must be non-null and point to at least `len` initialized bytes that
/// remain readable for the duration of this call. The caller retains ownership
/// of the input buffer and must release it separately.
#[no_mangle]
pub unsafe extern "C" fn check(ptr: *const u8, len: u32) -> u64 {
    let bytes = std::slice::from_raw_parts(ptr, len as usize);
    let result = match std::str::from_utf8(bytes) {
        Ok(source) => analyze_module_with_options(source, FrontendOptions::default()).to_json(),
        Err(_) => r#"{"checked":false,"diagnostics":[],"goals":[]}"#.into(),
    };
    let output = result.into_bytes().into_boxed_slice();
    let size = output.len() as u64;
    let result_ptr = Box::into_raw(output) as *mut u8 as u32 as u64;
    (size << 32) | result_ptr
}
