#![cfg_attr(test, allow(unused_imports, dead_code))]
use std::borrow::{Borrow, BorrowMut};
#[cfg(not(no_global_oom_handling))]
use std::cmp::Ordering::{self, Less};
#[cfg(not(no_global_oom_handling))]
use std::mem;
#[cfg(not(no_global_oom_handling))]
use std::mem::size_of;
#[cfg(not(no_global_oom_handling))]
use std::ptr;

use std::borrow::ToOwned;
use std::boxed::Box;
use std::vec::Vec;

pub fn main() {

}

#[cfg(not(no_global_oom_handling))]
fn insert_head<T, F>(v: &mut [T], is_less: &mut F)
where
    F: FnMut(&T, &T) -> bool,
{
    if v.len() >= 2 && is_less(&v[1], &v[0]) {
        unsafe {
            let mut tmp = mem::ManuallyDrop::new(ptr::read(&v[0]));
            
            let mut hole = InsertionHole { src: &mut *tmp, dest: &mut v[1] };
            ptr::copy_nonoverlapping(&v[1], &mut v[0], 1);

            for i in 2..v.len() {
                if !is_less(&v[i], &*tmp) {
                    break;
                }
                ptr::copy_nonoverlapping(&v[i], &mut v[i - 1], 1);
                hole.dest = &mut v[i];
            }
        }
    }

    struct InsertionHole<T> {
        src: *mut T,
        dest: *mut T,
    }

    impl<T> Drop for InsertionHole<T> {
        fn drop(&mut self) {
            unsafe {
                ptr::copy_nonoverlapping(self.src, self.dest, 1);
            }
        }
    }
}

#[cfg(not(no_global_oom_handling))]
unsafe fn merge<T, F>(v: &mut [T], mid: usize, buf: *mut T, is_less: &mut F)
where
    F: FnMut(&T, &T) -> bool,
{
    let len = v.len();
    let v = v.as_mut_ptr();
    let (v_mid, v_end) = unsafe { (v.add(mid), v.add(len)) };

    let mut hole;

    if mid <= len - mid {
        unsafe {
            ptr::copy_nonoverlapping(v, buf, mid);
            hole = MergeHole { start: buf, end: buf.add(mid), dest: v };
        }

        let left = &mut hole.start;
        let mut right = v_mid;
        let out = &mut hole.dest;

        while *left < hole.end && right < v_end {
            unsafe {
                let to_copy = if is_less(&*right, &**left) {
                    get_and_increment(&mut right)
                } else {
                    get_and_increment(left)
                };
                ptr::copy_nonoverlapping(to_copy, get_and_increment(out), 1);
            }
        }
    } else {
        unsafe {
            ptr::copy_nonoverlapping(v_mid, buf, len - mid);
            hole = MergeHole { start: buf, end: buf.add(len - mid), dest: v_mid };
        }

        let left = &mut hole.dest;
        let right = &mut hole.end;
        let mut out = v_end;

        while v < *left && buf < *right {
            unsafe {
                let to_copy = if is_less(&*right.offset(-1), &*left.offset(-1)) {
                    decrement_and_get(left)
                } else {
                    decrement_and_get(right)
                };
                ptr::copy_nonoverlapping(to_copy, decrement_and_get(&mut out), 1);
            }
        }
    }
    
    unsafe fn get_and_increment<T>(ptr: &mut *mut T) -> *mut T {
        let old = *ptr;
        *ptr = unsafe { ptr.offset(1) };
        old
    }

    unsafe fn decrement_and_get<T>(ptr: &mut *mut T) -> *mut T {
        *ptr = unsafe { ptr.offset(-1) };
        *ptr
    }

    struct MergeHole<T> {
        start: *mut T,
        end: *mut T,
        dest: *mut T,
    }

    impl<T> Drop for MergeHole<T> {
        fn drop(&mut self) {
            // `T` is not a zero-sized type, so it's okay to divide by its size.
            let len = (self.end as usize - self.start as usize) / mem::size_of::<T>();
            unsafe {
                ptr::copy_nonoverlapping(self.start, self.dest, len);
            }
        }
    }
}

#[cfg(not(no_global_oom_handling))]
fn merge_sort<T, F>(v: &mut [T], mut is_less: F)
where
    F: FnMut(&T, &T) -> bool,
{
    const MAX_INSERTION: usize = 20;
    const MIN_RUN: usize = 10;

    if size_of::<T>() == 0 {
        return;
    }

    let len = v.len();

    if len <= MAX_INSERTION {
        if len >= 2 {
            for i in (0..len - 1).rev() {
                insert_head(&mut v[i..], &mut is_less);
            }
        }
        return;
    }

    let mut buf = Vec::with_capacity(len / 2);

    let mut runs = vec![];
    let mut end = len;
    while end > 0 {
        let mut start = end - 1;
        if start > 0 {
            start -= 1;
            unsafe {
                if is_less(v.get_unchecked(start + 1), v.get_unchecked(start)) {
                    while start > 0 && is_less(v.get_unchecked(start), v.get_unchecked(start - 1)) {
                        start -= 1;
                    }
                    v[start..end].reverse();
                } else {
                    while start > 0 && !is_less(v.get_unchecked(start), v.get_unchecked(start - 1))
                    {
                        start -= 1;
                    }
                }
            }
        }

        while start > 0 && end - start < MIN_RUN {
            start -= 1;
            insert_head(&mut v[start..end], &mut is_less);
        }

        runs.push(Run { start, len: end - start });
        end = start;

        while let Some(r) = collapse(&runs) {
            let left = runs[r + 1];
            let right = runs[r];
            unsafe {
                merge(
                    &mut v[left.start..right.start + right.len],
                    left.len,
                    buf.as_mut_ptr(),
                    &mut is_less,
                );
            }
            runs[r] = Run { start: left.start, len: left.len + right.len };
            runs.remove(r + 1);
        }
    }

    debug_assert!(runs.len() == 1 && runs[0].start == 0 && runs[0].len == len);

    #[inline]
    fn collapse(runs: &[Run]) -> Option<usize> {
        let n = runs.len();
        if n >= 2
            && (runs[n - 1].start == 0
                || runs[n - 2].len <= runs[n - 1].len
                || (n >= 3 && runs[n - 3].len <= runs[n - 2].len + runs[n - 1].len)
                || (n >= 4 && runs[n - 4].len <= runs[n - 3].len + runs[n - 2].len))
        {
            if n >= 3 && runs[n - 3].len < runs[n - 1].len { Some(n - 3) } else { Some(n - 2) }
        } else {
            None
        }
    }

    #[derive(Clone, Copy)]
    struct Run {
        start: usize,
        len: usize,
    }
}