// This is adapted from `fallback.rs` from rust-memchr. It's modified to return
// the 'inverse' query of memchr, e.g. finding the first byte not in the provided
// set. This is simple for the 1-byte case.

use core::cmp;
use core::ptr;
use core::usize;

#[cfg(target_pointer_width = "32")]
const USIZE_BYTES: usize = 4;

#[cfg(target_pointer_width = "64")]
const USIZE_BYTES: usize = 8;

// The number of bytes to loop at in one iteration of memchr/memrchr.
const LOOP_SIZE: usize = 2 * USIZE_BYTES;

/// Repeat the given byte into a word size number. That is, every 8 bits
/// is equivalent to the given byte. For example, if `b` is `\x4E` or
/// `01001110` in binary, then the returned value on a 32-bit system would be:
/// `01001110_01001110_01001110_01001110`.
#[inline(always)]
fn repeat_byte(b: u8) -> usize {
    (b as usize) * (usize::MAX / 255)
}

pub fn inv_memchr(n1: u8, haystack: &[u8]) -> Option<usize> {
    let vn1 = repeat_byte(n1);
    let confirm = |byte| byte != n1;
    let loop_size = cmp::min(LOOP_SIZE, haystack.len());
    let align = USIZE_BYTES - 1;
    let start_ptr = haystack.as_ptr();
    let end_ptr = haystack[haystack.len()..].as_ptr();
    let mut ptr = start_ptr;

    unsafe {
        if haystack.len() < USIZE_BYTES {
            return forward_search(start_ptr, end_ptr, ptr, confirm);
        }

        let chunk = read_unaligned_usize(ptr);
        if (chunk ^ vn1) != 0 {
            return forward_search(start_ptr, end_ptr, ptr, confirm);
        }

        ptr = ptr_add(ptr, USIZE_BYTES - (start_ptr as usize & align));
        debug_assert!(ptr > start_ptr);
        debug_assert!(ptr_sub(end_ptr, USIZE_BYTES) >= start_ptr);
        while loop_size == LOOP_SIZE && ptr <= ptr_sub(end_ptr, loop_size) {
            debug_assert_eq!(0, (ptr as usize) % USIZE_BYTES);

            let a = *(ptr as *const usize);
            let b = *(ptr_add(ptr, USIZE_BYTES) as *const usize);
            let eqa = (a ^ vn1) != 0;
            let eqb = (b ^ vn1) != 0;
            if eqa || eqb {
                break;
            }
            ptr = ptr_add(ptr, LOOP_SIZE);
        }
        forward_search(start_ptr, end_ptr, ptr, confirm)
    }
}

/// Return the last index not matching the byte `x` in `text`.
pub fn inv_memrchr(n1: u8, haystack: &[u8]) -> Option<usize> {
    let vn1 = repeat_byte(n1);
    let confirm = |byte| byte != n1;
    let loop_size = cmp::min(LOOP_SIZE, haystack.len());
    let align = USIZE_BYTES - 1;
    let start_ptr = haystack.as_ptr();
    let end_ptr = haystack[haystack.len()..].as_ptr();
    let mut ptr = end_ptr;

    unsafe {
        if haystack.len() < USIZE_BYTES {
            return reverse_search(start_ptr, end_ptr, ptr, confirm);
        }

        let chunk = read_unaligned_usize(ptr_sub(ptr, USIZE_BYTES));
        if (chunk ^ vn1) != 0 {
            return reverse_search(start_ptr, end_ptr, ptr, confirm);
        }

        ptr = (end_ptr as usize & !align) as *const u8;
        debug_assert!(start_ptr <= ptr && ptr <= end_ptr);
        while loop_size == LOOP_SIZE && ptr >= ptr_add(start_ptr, loop_size) {
            debug_assert_eq!(0, (ptr as usize) % USIZE_BYTES);

            let a = *(ptr_sub(ptr, 2 * USIZE_BYTES) as *const usize);
            let b = *(ptr_sub(ptr, 1 * USIZE_BYTES) as *const usize);
            let eqa = (a ^ vn1) != 0;
            let eqb = (b ^ vn1) != 0;
            if eqa || eqb {
                break;
            }
            ptr = ptr_sub(ptr, loop_size);
        }
        reverse_search(start_ptr, end_ptr, ptr, confirm)
    }
}

#[inline(always)]
unsafe fn forward_search<F: Fn(u8) -> bool>(
    start_ptr: *const u8,
    end_ptr: *const u8,
    mut ptr: *const u8,
    confirm: F,
) -> Option<usize> {
    debug_assert!(start_ptr <= ptr);
    debug_assert!(ptr <= end_ptr);

    while ptr < end_ptr {
        if confirm(*ptr) {
            return Some(sub(ptr, start_ptr));
        }
        ptr = ptr.offset(1);
    }
    None
}

#[inline(always)]
unsafe fn reverse_search<F: Fn(u8) -> bool>(
    start_ptr: *const u8,
    end_ptr: *const u8,
    mut ptr: *const u8,
    confirm: F,
) -> Option<usize> {
    debug_assert!(start_ptr <= ptr);
    debug_assert!(ptr <= end_ptr);

    while ptr > start_ptr {
        ptr = ptr.offset(-1);
        if confirm(*ptr) {
            return Some(sub(ptr, start_ptr));
        }
    }
    None
}

/// Increment the given pointer by the given amount.
unsafe fn ptr_add(ptr: *const u8, amt: usize) -> *const u8 {
    debug_assert!(amt < ::core::isize::MAX as usize);
    ptr.offset(amt as isize)
}

/// Decrement the given pointer by the given amount.
unsafe fn ptr_sub(ptr: *const u8, amt: usize) -> *const u8 {
    debug_assert!(amt < ::core::isize::MAX as usize);
    ptr.offset((amt as isize).wrapping_neg())
}

unsafe fn read_unaligned_usize(ptr: *const u8) -> usize {
    let mut n: usize = 0;
    ptr::copy_nonoverlapping(ptr, &mut n as *mut _ as *mut u8, USIZE_BYTES);
    n
}

/// Subtract `b` from `a` and return the difference. `a` should be greater than
/// or equal to `b`.
fn sub(a: *const u8, b: *const u8) -> usize {
    debug_assert!(a >= b);
    (a as usize) - (b as usize)
}

/// Safe wrapper around `forward_search`
#[inline]
pub(super) fn forward_search_bytes<F: Fn(u8) -> bool>(
    s: &[u8],
    confirm: F,
) -> Option<usize> {
    unsafe {
        let start = s.as_ptr();
        let end = start.add(s.len());
        forward_search(start, end, start, confirm)
    }
}

/// Safe wrapper around `reverse_search`
#[inline]
pub(super) fn reverse_search_bytes<F: Fn(u8) -> bool>(
    s: &[u8],
    confirm: F,
) -> Option<usize> {
    unsafe {
        let start = s.as_ptr();
        let end = start.add(s.len());
        reverse_search(start, end, end, confirm)
    }
}
