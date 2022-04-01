extern crate prusti_contracts;
use prusti_contracts::*;

use std::vec::Vec;

pub fn main() {
    let mut x : [i32; 50] = [5; 50];
    merge_sort(&mut x);
}

fn insert_head(v: &mut [i32]) {
    if v.len() >= 2 && (v[1] < v[0]) {
        let tmp = v[0];
        v[0] = v[1];
        let mut i = 2;
        while i < v.len() {
            body_invariant!(i >= 2 && i < v.len());
            if !(i < v.len() && v[i] < tmp) {
                break;
            }
            v[i - 1] = v[i];
            i += 1;
        }
        v[i - 1] = tmp;
    }
}

struct Buf{
    v: Vec<i32>,
}

impl Buf {
    #[trusted]
    #[pure]
    #[ensures(result >= 0)]
    pub fn len(&self) -> usize {
        self.v.len()
    }

    #[trusted]
    #[requires(0 <= index && index < self.len())]
    pub fn index(&self, index: usize) -> i32 {
        self.v[index]
    }

    #[trusted]
    pub fn push(&mut self, value: i32) {
        self.v.push(value);
    }
}

#[requires(mid >= 0 && mid <= v.len())]
fn merge(v: &mut [i32], mid: usize, buf: &mut Buf) {
    let len = v.len();

    if mid <= len - mid {
        let mut i = 0;
        while i < mid {
            body_invariant!(i >= 0 && i < v.len());
            buf.push(v[i]);
            i += 1;
        }

        let mut left = 0;
        let mut right = mid;
        let mut out = 0;
        
        while left < mid && right < len {
            body_invariant!(len <= v.len() && right < len && left < len);
            body_invariant!(left + right - mid < v.len());
            body_invariant!(out <= left + right - mid);
            body_invariant!(out < v.len());
            if v[right] < v[left] {
                v[out] = v[right];
                right += 1;
            } else {
                v[out] = buf.index(left);
                left += 1;
            }
            out += 1;
        }

        while left < mid {
            v[out] = buf.index(left);
            out += 1;
            left += 1;
        }

    } else {
        let mut i = mid;
        while i < len {
            buf.push(v[i]);
            i += 1;
        }

        let mut left = mid;
        let mut right = len - mid;
        let mut out = len;

        let argument = 0;
        while v[0] < v[left] && buf.index(argument) < buf.index(right) {
            out -= 1;
            if buf.index(right - 1) < v[left - 1] {
                left -= 1;
                v[out] = v[left];
            } else {
                right -= 1;
                v[out] = buf.index(right);
            }
        }

        let mut i = 0;
        while i < right {
            v[left] = buf.index(i);
            i += 1;
            left += 1;
        }
    }
}

#[derive(Clone, Copy)]
struct Run {
    start: usize,
    len: usize,
}

struct Runs{
    v: Vec<Run>,
}

impl Runs {
    #[trusted]
    #[pure]
    #[ensures(result >= 0)]
    pub fn len(&self) -> usize {
        self.v.len()
    }

    #[trusted]
    #[requires(0 <= index && index < self.len())]
    pub fn index(&self, index: usize) -> &Run {
        &self.v[index]
    }

    #[trusted]
    #[requires(0 <= index && index < self.len())]
    pub fn assign(&mut self, index: usize, value: Run) {
        self.v[index] = value;
    }

    #[trusted]
    pub fn push(&mut self, value: Run) {
        self.v.push(value);
    }

    #[trusted]
    #[requires(0 <= index && index < self.len())]
    pub fn remove(&mut self, index: usize) {
        self.v.remove(index);
    }
}

fn collapse(runs: &Runs) -> usize {
    let n = runs.len();
    if n >= 2
        && (runs.index(n - 1).start == 0
            || runs.index(n - 2).len <= runs.index(n - 1).len
            || (n >= 3 && runs.index(n - 3).len <= runs.index(n - 2).len + runs.index(n - 1).len)
            || (n >= 4 && runs.index(n - 4).len <= runs.index(n - 3).len + runs.index(n - 2).len))
    {
        if n >= 3 && runs.index(n - 3).len < runs.index(n - 1).len { n - 3 } else { n - 2 }
    } else {
        n
    }
}

fn merge_sort(v: &mut [i32]) {
    const MAX_INSERTION: usize = 20;
    const MIN_RUN: usize = 10;

    if v.len() == 0 {
        return;
    }

    let len = v.len();

    if len <= MAX_INSERTION {
        if len >= 2 {
            let mut i = len - 2;
            loop {
                insert_head(&mut v[i..]);
                if i == 0 {
                    break;
                } else {
                    i -= 1;
                }
            }
        }
        return;
    }

    let mut buf = Buf{v: Vec::with_capacity(len / 2)};

    let mut runs = Runs{v: vec![]};
    let mut end = len;
    while end > 0 {
        let mut start = end - 1;
        if start > 0 {
            start -= 1;
                if v.get(start + 1) < v.get(start) {
                    while start > 0 && v.get(start) < v.get(start - 1) {
                        start -= 1;
                    }
                    v[start..end].reverse();
                } else {
                    while start > 0 && !(v.get(start) < v.get(start - 1))
                    {
                        start -= 1;
                    }
                }
        }

        while start > 0 && end - start < MIN_RUN {
            start -= 1;
            insert_head(&mut v[start..end]);
        }

        runs.push(Run { start, len: end - start });
        end = start;

        loop {
            let r = collapse(&runs);
            if r == runs.len() {
                break;
            }
            let left = runs.index(r + 1);
            let right = runs.index(r);
            merge(
                &mut v[left.start..right.start + right.len],
                left.len,
                &mut buf,
            );
            runs.assign(r, Run { start: left.start, len: left.len + right.len });
            runs.remove(r + 1);
        }
    }

    debug_assert!(runs.len() == 1 && runs.index(0).start == 0 && runs.index(0).len == len);
}