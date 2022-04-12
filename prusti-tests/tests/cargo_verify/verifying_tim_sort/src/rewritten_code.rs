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
    #[ensures(self.len() == old(self).len())]
    pub fn index(&self, index: usize) -> i32 {
        self.v[index]
    }

    #[trusted]
    #[ensures(self.len() == old(self).len() + 1)]
    pub fn push(&mut self, value: i32) {
        self.v.push(value);
    }
}

#[requires(mid >= 0 && mid <= v.len() && buf.len() == 0)]
fn merge(v: &mut [i32], mid: usize, buf: &mut Buf) {
    let len = v.len();
    assert!(len == v.len());
    if mid <= len - mid {
        let mut i = 0;
        while i < mid {
            body_invariant!(i < mid);
            body_invariant!(buf.len() == i);
            body_invariant!(buf.len() < mid);
            buf.push(v[i]);
            i += 1;
            assert!(buf.len() <= mid);
        }
        assert!(buf.len() == mid);

        let mut left = 0;
        let mut right = mid;
        let mut out = 0;
        
        while left < mid && right < len {
            body_invariant!(right < len);
            body_invariant!(right < v.len());
            
            body_invariant!(left < mid);
            body_invariant!(left < buf.len());
            
            body_invariant!(left + right - mid < v.len());
            body_invariant!(out <= left + right - mid);
            body_invariant!(out < v.len());
            
            if v[right] < buf.index(left) {
                v[out] = v[right];
                right += 1;
            } else {
                v[out] = buf.index(left);
                left += 1;
            }
            out += 1;
        }

        while left < mid {
            body_invariant!(left < mid);
            body_invariant!(v.len() - out >= mid - left);
            body_invariant!(out < v.len());
            
            body_invariant!(left < mid);
            body_invariant!(left < buf.len());

            v[out] = buf.index(left);
            out += 1;
            left += 1;
        }
    } else {
        let mut i = mid;
        while i < len {
            body_invariant!(i >= mid && i < len);
            body_invariant!(buf.len() == i - mid);
            body_invariant!(buf.len() < len - mid);
            buf.push(v[i]);
            i += 1;
            assert!(buf.len() <= len - mid);
        }
        assert!(buf.len() == len - mid);

        let mut left = mid;
        let mut right = len - mid;
        let mut out = len;

        while left > 0 && right > 0 {
            body_invariant!(left >= 1);
            body_invariant!(mid <= v.len());
            body_invariant!(left <= mid);
            body_invariant!(left <= v.len());
            
            body_invariant!(right >= 1);
            body_invariant!(right <= len - mid);
            body_invariant!(right <= buf.len());
            
            body_invariant!(out <= v.len());
            body_invariant!(left + right > 0);
            body_invariant!(out == left + right);
            body_invariant!(out > 0);

            out -= 1;
            if buf.index(right - 1) < v[left - 1] {
                left -= 1;
                v[out] = v[left];
            } else {
                right -= 1;
                v[out] = buf.index(right);
            }
        }

        while right > 0 {
            body_invariant!(right >= 1);
           
            body_invariant!(right <= len - mid);
            body_invariant!(right <= buf.len());

            body_invariant!(right <= len);
            body_invariant!(right <= v.len());

            right -= 1;
            v[right] = buf.index(right);
        }
    }
}

#[derive(Clone, Copy)]
struct Run {
    start: usize,
    len: usize,
    array_size: usize,
}

impl Run {
    #[trusted]
    #[pure]
    #[ensures(result >= 0)]
    pub fn len(&self) -> usize {
        self.len
    }

    #[trusted]
    #[pure]
    #[ensures(result >= 0)]
    pub fn start(&self) -> usize {
        self.start
    }

    #[trusted]
    #[pure]
    #[ensures(result >= 0)]
    pub fn array_size(&self) -> usize {
        self.array_size
    }

    #[trusted]
    #[pure]
    #[ensures(result >= 0 && result <= self.array_size())]
    pub fn run_last_index_exclusive(&self) -> usize {
        self.len() + self.start()
    }
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
    #[ensures(self.len() == old(self).len())]
    pub fn index(&self, index: usize) -> &Run {
        &self.v[index]
    }

    #[trusted]
    #[requires(0 <= index && index < self.len())]
    pub fn assign(&mut self, index: usize, value: Run) {
        self.v[index] = value;
    }

    #[trusted]
    #[ensures(self.len() == old(self).len() + 1)]
    pub fn push(&mut self, value: Run) {
        self.v.push(value);
    }

    #[trusted]
    #[requires(0 <= index && index < self.len())]
    #[ensures(self.len() == old(self).len() - 1)]
    pub fn remove(&mut self, index: usize) {
        self.v.remove(index);
    }
}

#[ensures(result == runs.len() || (runs.len() > 1 && result < runs.len() - 1))]
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
    assert!(len == v.len());

    if len <= MAX_INSERTION {
        if len >= 2 {
            let mut i = len - 2;
            loop {
                body_invariant!(i >= 0);
                insert_head(&mut v[i..]);
                if i == 0 {
                    break;
                } else {
                    assert!(i > 0);
                    i -= 1;
                }
            }
        }
        return;
    }

    let mut buf = Buf{v: Vec::with_capacity(len / 2)};
    let mut runs = Runs{v: vec![]};
    let mut end = len;
    assert!(end == v.len());

    while end > 0 {
        body_invariant!(end >= 1 && end <= v.len());
        let mut start = end - 1;

        if start > 0 {
            start -= 1;
            assert!(start < end - 1);
            assert!(end <= v.len());
            assert!(start < v.len() - 1);
            if v[start + 1] < v[start] {
                while start > 0 {
                    body_invariant!(start >= 1 && start < v.len() - 1);
                    if !(v[start] < v[start - 1]) {
                        break;
                    }
                    start -= 1;
                }
                v[start..end].reverse();
            } else {
                while start > 0 {
                    body_invariant!(start >= 1 && start < v.len() - 1);
                    if v[start] < v[start - 1] {
                        break;
                    }
                    start -= 1;
                }
            }
        }

        while start > 0 && end - start < MIN_RUN {
            body_invariant!(start >= 1);
            start -= 1;
            insert_head(&mut v[start..end]);
        }
        
        runs.push(Run { start, len: end - start, array_size: len });
        end = start;
        
        loop {
            let r = collapse(&runs);
            assert!(r == runs.len() || (runs.len() > 1 && r < runs.len() - 1));
            if r == runs.len() {
                assert!(r == runs.len());
                break;
            } else if runs.len() > 1 && r < runs.len() - 1 {
                assert!(runs.len() > 1 && r < runs.len() - 1);
                let left = runs.index(r + 1);
                let right = runs.index(r);
                merge(
                    &mut v[left.start..right.run_last_index_exclusive()],
                    left.len,
                    &mut buf,
                );
                //runs.assign(r, Run { start: left.start, len: left.len + right.len, array_size: len });
                runs.remove(r + 1);
            }
        }
    }
    
    //debug_assert!(runs.len() == 1 && runs.index(0).start == 0 && runs.index(0).len == len);
}