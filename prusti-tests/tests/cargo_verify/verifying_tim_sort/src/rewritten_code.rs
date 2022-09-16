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
    #[ensures(result.len() == 0)]
    pub fn new(len: usize) -> Buf {
        Buf {v: Vec::with_capacity(len / 2)}
    }

    #[trusted]
    #[pure]
    #[ensures(result >= 0)]
    pub fn len(&self) -> usize {
        self.v.len()
    }

    #[trusted]
    #[pure]
    #[requires(0 <= index && index < self.len())]
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
#[ensures(v.len() == old(v.len()))]
fn merge(v: &mut [i32], mid: usize, buf: &mut Buf) {
    let len = v.len();
    if mid <= len - mid {
        let mut i = 0;
        while i < mid {
            body_invariant!(v.len() == len);

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
            body_invariant!(v.len() == len);

            body_invariant!(right < len);
            body_invariant!(len == v.len());
            body_invariant!(right < v.len());
            
            body_invariant!(left < mid);
            body_invariant!(buf.len() == mid);
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

        assert!(v.len() == len);
        
        while left < mid {
            body_invariant!(v.len() == len);

            body_invariant!(left < mid);
            body_invariant!(v.len() - out >= mid - left);
            body_invariant!(out < v.len());
            
            body_invariant!(left < mid);
            body_invariant!(buf.len() == mid);
            body_invariant!(left < buf.len());

            v[out] = buf.index(left);
            out += 1;
            left += 1;
        }

        assert!(v.len() == len);
    } else {
        let mut i = mid;
        while i < len {
            body_invariant!(v.len() == len);

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
            body_invariant!(v.len() == len);

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

        assert!(v.len() == len);

        while right > 0 {
            body_invariant!(v.len() == len);

            body_invariant!(right >= 1);
           
            body_invariant!(right <= len - mid);
            body_invariant!(right <= buf.len());

            body_invariant!(right <= len);
            body_invariant!(right <= v.len());

            right -= 1;
            v[right] = buf.index(right);
        }

        assert!(v.len() == len);
    }
}

struct Runs{
    start: Vec<usize>,
    len: Vec<usize>,
    runs_sum_cur: usize,
    runs_sum_max: usize,
}

impl Runs {
    #[trusted]
    #[requires(runs_sum_max <= usize::MAX)]
    #[ensures(result.len() == 0)]
    #[ensures(result.get_runs_sum_cur() == 0)]
    #[ensures(result.get_runs_sum_max() == runs_sum_max)]
    pub fn new(runs_sum_max: usize) -> Runs {
        Runs {start: vec![], len: vec![], runs_sum_cur: 0, runs_sum_max}
    }

    #[trusted]
    #[pure]
    #[ensures(result >= 0)]
    pub fn len(&self) -> usize {
        self.len.len()
    }

    #[pure]
    pub fn get_runs_sum_cur(&self) -> usize {
        self.runs_sum_cur
    }

    #[pure]
    pub fn get_runs_sum_max(&self) -> usize {
        self.runs_sum_max
    }
    
    #[requires(self.get_runs_sum_cur() + value <= self.get_runs_sum_max())]
    #[ensures(self.get_runs_sum_cur() == old(self.get_runs_sum_cur()) + value)]
    #[ensures(self.get_runs_sum_cur() <= self.get_runs_sum_max())]
    pub fn add_runs_sum_cur(&mut self, value: usize) {
        self.runs_sum_cur += value;
    }

    #[pure]
    #[trusted]
    #[requires(0 <= index && index < self.len())]
    pub fn index_start(&self, index: usize) -> usize {
        self.start[index]
    }

    #[pure]
    #[trusted]
    #[requires(0 <= index && index < self.len())]
    pub fn index_len(&self, index: usize) -> usize {
        self.len[index]
    }
    
    #[trusted]
    #[requires(forall(|i: usize| (0 <= i && i < self.len() ==> self.index_len(i) <= self.get_runs_sum_cur())))]
    #[requires(self.get_runs_sum_cur() + new_len <= self.get_runs_sum_max())]
    #[requires(forall(|i: usize| (0 <= i && i < self.len() ==> self.index_len(i) + new_len <= self.get_runs_sum_max())))]
    #[requires(forall(|i: usize, j: usize| (0 <= i && i < self.len() && i < j && j < self.len() ==> self.index_len(i) + self.index_len(j) <= self.get_runs_sum_max())))]
    #[requires(forall(|i: usize, j: usize| (self.len() < 2 || (self.len() >= 2 && 0 <= i && i < (self.len() - 1) && j == (i + 1) ==> self.index_start(i) > self.index_start(j)))))]
    #[requires(self.len() == 0 || self.index_start(self.len() - 1) == self.get_runs_sum_max() - self.get_runs_sum_cur())]
    #[requires(self.len() == 0 || new_start < self.index_start(self.len() - 1))]
    #[requires(self.len() < 1 || new_start + new_len == self.index_start(self.len() - 1))]
    #[requires(forall(|i: usize, j: usize| (self.len() < 2 || (self.len() >= 2 &&  0 <= i && i < (self.len() - 1) && j == (i + 1) ==> self.index_start(j) + self.index_len(j) == self.index_start(i)))))]
    #[ensures(self.len() == old(self.len()) + 1)]
    #[ensures(self.index_len(self.len() - 1) == new_len)]
    #[ensures(self.get_runs_sum_cur() == new_len + old(self.get_runs_sum_cur()))]
    #[ensures(self.get_runs_sum_max() == old(self.get_runs_sum_max()))]
    #[ensures(forall(|i: usize| (0 <= i && i < self.len() ==> self.index_len(i) <= self.get_runs_sum_cur())))]
    #[ensures(forall(|i: usize, j: usize| (0 <= i && i < self.len() && i < j && j < self.len() ==> self.index_len(i) + self.index_len(j) <= self.get_runs_sum_max())))]
    #[ensures(forall(|i: usize, j: usize| (self.len() < 2 || (self.len() >= 2 && 0 <= i && i < (self.len() - 1) && j == (i + 1) ==> self.index_start(i) > self.index_start(j)))))]
    #[ensures(self.index_start(self.len() - 1) == self.get_runs_sum_max() - self.get_runs_sum_cur())]
    #[ensures(forall(|i: usize, j: usize| (self.len() < 2 || (self.len() >= 2 &&  0 <= i && i < (self.len() - 1) && j == (i + 1) ==> self.index_start(j) + self.index_len(j) == self.index_start(i)))))]
    pub fn push(&mut self, new_start: usize, new_len: usize) {
        self.add_runs_sum_cur(new_len);
        self.start.push(new_start);
        self.len.push(new_len);
    }


    #[trusted]
    #[requires(0 <= index && index < self.len() - 1)]
    #[requires(forall(|i: usize| (0 <= i && i < self.len() ==> self.index_len(i) <= self.get_runs_sum_cur())))]
    #[requires(forall(|i: usize, j: usize| (0 <= i && i < self.len() && i < j && j < self.len() ==> self.index_len(i) + self.index_len(j) <= self.get_runs_sum_max())))]
    #[requires(forall(|i: usize| (0 <= i && i < self.len() ==> self.index_len(i) + self.index_start(i) <= self.get_runs_sum_max())))]
    #[requires(forall(|i: usize, j: usize| (self.len() < 2 || (self.len() >= 2 && 0 <= i && i < (self.len() - 1) && j == (i + 1) ==> self.index_start(i) > self.index_start(j)))))]
    #[requires(self.index_start(self.len() - 1) == self.get_runs_sum_max() - self.get_runs_sum_cur())]
    #[requires(forall(|i: usize, j: usize| (self.len() < 2 || (self.len() >= 2 &&  0 <= i && i < (self.len() - 1) && j == (i + 1) ==> self.index_start(j) + self.index_len(j) == self.index_start(i)))))]
    #[ensures(self.len() == old(self.len()) - 1)]
    #[ensures(self.index_len(index) == old(self.index_len(index)) + old(self.index_len(index + 1)))]
    #[ensures(self.get_runs_sum_cur() == old(self.get_runs_sum_cur()))]
    #[ensures(self.get_runs_sum_max() == old(self.get_runs_sum_max()))]
    #[ensures(forall(|i: usize| (0 <= i && i < self.len() ==> self.index_len(i) <= self.get_runs_sum_cur())))]
    #[ensures(forall(|i: usize, j: usize| (0 <= i && i < self.len() && i < j && j < self.len() ==> self.index_len(i) + self.index_len(j) <= self.get_runs_sum_max())))]
    #[ensures(forall(|i: usize| (0 <= i && i < self.len() ==> self.index_len(i) + self.index_start(i) <= self.get_runs_sum_max())))]
    #[ensures(forall(|i: usize, j: usize| (self.len() < 2 || (self.len() >= 2 && 0 <= i && i < (self.len() - 1) && j == (i + 1) ==> self.index_start(i) > self.index_start(j)))))]
    #[ensures(self.index_start(self.len() - 1) == self.get_runs_sum_max() - self.get_runs_sum_cur())]
    #[ensures(forall(|i: usize, j: usize| (self.len() < 2 || (self.len() >= 2 &&  0 <= i && i < (self.len() - 1) && j == (i + 1) ==> self.index_start(j) + self.index_len(j) == self.index_start(i)))))]
    pub fn merge(&mut self, index: usize) {
        let new_start = self.index_start(index + 1);
        let new_len = self.index_len(index) + self.index_len(index + 1);
        self.start[index] = new_start;
        self.len[index] = new_len;
        self.start.remove(index + 1);
        self.len.remove(index + 1);
    }
}

#[trusted]
#[requires(forall(|i: usize, j: usize| (0 <= i && i < runs.len() && i < j && j < runs.len() ==> runs.index_len(i) + runs.index_len(j) <= runs.get_runs_sum_max())))]
#[ensures(result == runs.len() || (runs.len() > 1 && result < runs.len() - 1))]
fn collapse(runs: &Runs) -> usize {
    let n = runs.len();
    if n >= 2 {
        assert!(n >= 2 && n <= runs.len());
        if runs.index_start(n - 1) == 0 {
            return n - 2;
        } else if runs.index_len(n - 2) <= runs.index_len(n - 1) {
            return n - 2;
        } else if n >= 3 {
            assert!(n >= 3 && n <= runs.len());
            assert!(runs.index_len(n - 2) <= usize::MAX);
            if runs.index_len(n - 3) <= runs.index_len(n - 2) + runs.index_len(n - 1) {
                if runs.index_len(n - 3) < runs.index_len(n - 1) {
                    return n - 3;
                } else {
                    return n - 2;
                }
            } else if n >= 4 {
                assert!(n >= 4 && n <= runs.len());
                if runs.index_len(n - 4) <= runs.index_len(n - 3) + runs.index_len(n - 2) {
                    if runs.index_len(n - 3) < runs.index_len(n - 1) {
                        return n - 3;
                    } else {
                        return n - 2;
                    }
                }
            }
        }
    }
    return n;
}

#[trusted]
#[requires(2 * v.len() <= usize::MAX)]
fn sort_small_array(v: &mut [i32]) {
    let len = v.len();
    if len >= 2 {
        let mut i = len - 2;
        loop {
            body_invariant!(i >= 0);
            insert_head(&mut v[i..]);
            if i == 0 {
                break;
            } else {
                i -= 1;
            }
        }
    }
}

#[trusted]
#[requires(v.len() <= usize::MAX)]
#[requires(runs.get_runs_sum_max() == v.len())]
#[requires(end >= 1 && end <= v.len())]
#[requires(runs.get_runs_sum_cur() == v.len() - end)]
#[requires(MIN_RUN < 100)]
#[requires(forall(|i: usize| (0 <= i && i < runs.len() ==> runs.index_len(i) <= runs.get_runs_sum_cur())))]
#[requires(forall(|i: usize, j: usize| (0 <= i && i < runs.len() && i < j && j < runs.len() ==> runs.index_len(i) + runs.index_len(j) <= runs.get_runs_sum_max())))]
#[requires(forall(|i: usize| (0 <= i && i < runs.len() ==> runs.index_len(i) + runs.index_start(i) <= runs.get_runs_sum_max())))]
#[requires(forall(|i: usize, j: usize| (runs.len() < 2 || (runs.len() >= 2 && 0 <= i && i < (runs.len() - 1) && j == (i + 1) ==> runs.index_start(i) > runs.index_start(j)))))]
#[requires(runs.len() == 0 || runs.index_start(runs.len() - 1) == runs.get_runs_sum_max() - runs.get_runs_sum_cur())]
#[requires(forall(|i: usize, j: usize| (runs.len() < 2 || (runs.len() >= 2 &&  0 <= i && i < (runs.len() - 1) && j == (i + 1) ==> runs.index_start(j) + runs.index_len(j) == runs.index_start(i)))))]
#[ensures(runs.len() == old(runs.len()) + 1)]
#[ensures(forall(|i: usize| (0 <= i && i < runs.len() ==> runs.index_len(i) <= runs.get_runs_sum_cur())))]
#[ensures(forall(|i: usize, j: usize| (0 <= i && i < runs.len() && i < j && j < runs.len() ==> runs.index_len(i) + runs.index_len(j) <= runs.get_runs_sum_max())))]
#[ensures(forall(|i: usize| (0 <= i && i < runs.len() ==> runs.index_len(i) + runs.index_start(i) <= runs.get_runs_sum_max())))]
#[ensures(forall(|i: usize, j: usize| (runs.len() < 2 || (runs.len() >= 2 && 0 <= i && i < (runs.len() - 1) && j == (i + 1) ==> runs.index_start(i) > runs.index_start(j)))))]
#[ensures(runs.index_start(runs.len() - 1) == runs.get_runs_sum_max() - runs.get_runs_sum_cur())]
#[ensures(forall(|i: usize, j: usize| (runs.len() < 2 || (runs.len() >= 2 &&  0 <= i && i < (runs.len() - 1) && j == (i + 1) ==> runs.index_start(j) + runs.index_len(j) == runs.index_start(i)))))]
#[ensures(result >= 0 && result < v.len())]
#[ensures(runs.get_runs_sum_cur() == v.len() - result)]
#[ensures(runs.get_runs_sum_max() == old(runs.get_runs_sum_max()))]
#[ensures(v.len() == old(v.len()))]
#[ensures(runs.get_runs_sum_max() == v.len())]
fn push_new_run(v: &mut [i32], runs: &mut Runs, mut end: usize, MIN_RUN: usize) -> usize {
    let mut start = end - 1;
    assert!(start < end);
    
    if start > 0 {
        start -= 1;
        assert!(start < end - 1);
        assert!(end <= v.len());
        assert!(start < v.len() - 1);
        if v[start + 1] < v[start] {
            while start > 0 {
                body_invariant!(runs.get_runs_sum_cur() == v.len() - end);
                body_invariant!(start >= 1 && start < v.len() - 1 && start < end);
                if !(v[start] < v[start - 1]) {
                    break;
                }
                start -= 1;
            }
            v[start..end].reverse();
        } else {
            while start > 0 {
                body_invariant!(runs.get_runs_sum_cur() == v.len() - end);
                body_invariant!(start >= 1 && start < v.len() - 1 && start < end);
                if v[start] < v[start - 1] {
                    break;
                }
                start -= 1;
            }
        }
    }


    while start > 0 && end - start < MIN_RUN {
        body_invariant!(runs.get_runs_sum_cur() == v.len() - end);
        body_invariant!(start >= 1 && end <= v.len() && start < end);
        start -= 1;
        insert_head(&mut v[start..end]);
    }
    
    assert!(runs.get_runs_sum_cur() == v.len() - end);
    
    assert!(runs.len() == 0 || runs.index_start(runs.len() - 1) == runs.get_runs_sum_max() - runs.get_runs_sum_cur());
    assert!(runs.get_runs_sum_max() - runs.get_runs_sum_cur() == end);
    assert!(runs.len() == 0 || runs.index_start(runs.len() - 1) == end);
    assert!(start < end);
    assert!(runs.len() == 0 || start < runs.index_start(runs.len() - 1));

    let new_len = end - start;
    assert!(start + new_len <= v.len());
    assert!(start + new_len <= runs.get_runs_sum_max());
    
    assert!(start + new_len == end);
    assert!(start + new_len == runs.index_start(runs.len() - 1));

    runs.push(start, new_len);
    end = start;

    assert!(runs.get_runs_sum_cur() == v.len() - end);

    return end;
}

#[requires(v.len() <= usize::MAX)]
fn merge_sort(v: &mut [i32]) {
    const MAX_INSERTION: usize = 20;
    const MIN_RUN: usize = 10;
    let MIN_RUN_COPY = MIN_RUN;

    if v.len() == 0 {
        return;
    }

    let len = v.len();
    if len <= MAX_INSERTION {
        sort_small_array(v);
        return;
    }
    
    let mut buf = Buf::new(len / 2);
    let mut runs = Runs::new(v.len());
    
    assert!(v.len() >= 1);
    assert!(runs.len() == 0);
    assert!(runs.get_runs_sum_cur() == 0);
    assert!(runs.get_runs_sum_max() == v.len());
    
    let mut end = len;
    while end > 0 {
        body_invariant!(buf.len() == 0);
        body_invariant!(end >= 1 && end <= v.len());
        body_invariant!(runs.get_runs_sum_max() == v.len());
        body_invariant!(runs.get_runs_sum_cur() == v.len() - end);
        body_invariant!(runs.get_runs_sum_cur() < runs.get_runs_sum_max());
        body_invariant!(forall(|i: usize| (0 <= i && i < runs.len() ==> runs.index_len(i) <= runs.get_runs_sum_cur())));
        body_invariant!(forall(|i: usize, j: usize| (0 <= i && i < runs.len() && i < j && j < runs.len() ==> runs.index_len(i) + runs.index_len(j) <= runs.get_runs_sum_max())));
        body_invariant!(forall(|i: usize| (0 <= i && i < runs.len() ==> runs.index_len(i) + runs.index_start(i) <= runs.get_runs_sum_max())));
        body_invariant!(forall(|i: usize, j: usize| (runs.len() < 2 || (runs.len() >= 2 && 0 <= i && i < (runs.len() - 1) && j == (i + 1) ==> runs.index_start(i) > runs.index_start(j)))));
        body_invariant!(runs.len() == 0 || runs.index_start(runs.len() - 1) == runs.get_runs_sum_max() - runs.get_runs_sum_cur());
        body_invariant!(forall(|i: usize, j: usize| (runs.len() < 2 || (runs.len() >= 2 &&  0 <= i && i < (runs.len() - 1) && j == (i + 1) ==> runs.index_start(j) + runs.index_len(j) == runs.index_start(i)))));

        assert!(end >= 1 && end <= v.len());
        end = push_new_run(v, &mut runs, end, MIN_RUN_COPY);
        assert!(runs.get_runs_sum_cur() == v.len() - end);
        assert!(runs.get_runs_sum_max() == v.len());

        
        loop {
            body_invariant!(buf.len() == 0);
            body_invariant!(runs.get_runs_sum_max() == v.len());
            body_invariant!(runs.get_runs_sum_cur() == v.len() - end);
            body_invariant!(runs.get_runs_sum_cur() <= runs.get_runs_sum_max());
            body_invariant!(forall(|i: usize| (0 <= i && i < runs.len() ==> runs.index_len(i) <= runs.get_runs_sum_cur())));
            body_invariant!(forall(|i: usize, j: usize| (0 <= i && i < runs.len() && i < j && j < runs.len() ==> runs.index_len(i) + runs.index_len(j) <= runs.get_runs_sum_max())));
            body_invariant!(forall(|i: usize| (0 <= i && i < runs.len() ==> runs.index_len(i) + runs.index_start(i) <= runs.get_runs_sum_max())));
            body_invariant!(forall(|i: usize, j: usize| (runs.len() < 2 || (runs.len() >= 2 && 0 <= i && i < (runs.len() - 1) && j == (i + 1) ==> runs.index_start(i) > runs.index_start(j)))));
            body_invariant!(runs.len() == 0 || runs.index_start(runs.len() - 1) == runs.get_runs_sum_max() - runs.get_runs_sum_cur());
            body_invariant!(forall(|i: usize, j: usize| (runs.len() < 2 || (runs.len() >= 2 &&  0 <= i && i < (runs.len() - 1) && j == (i + 1) ==> runs.index_start(j) + runs.index_len(j) == runs.index_start(i)))));

            let r = collapse(&runs);
            assert!(r == runs.len() || (runs.len() > 1 && r < runs.len() - 1));
            
            if r == runs.len() {
                assert!(r == runs.len());
                break;
            } else if runs.len() > 1 && r < runs.len() - 1 {
                assert!(runs.len() > 1 && r < runs.len() - 1);
                let left_start = runs.index_start(r + 1);
                let left_len = runs.index_len(r + 1);
                let right_start = runs.index_start(r);
                let right_len = runs.index_len(r);
                
                assert!(left_start < right_start);
                assert!(right_start + right_len <= runs.get_runs_sum_max());
                assert!(right_start + right_len <= v.len());

                assert!(left_start + left_len == right_start);

                merge(
                    &mut v[left_start..right_start + right_len],
                    left_len,
                    &mut buf,
                );

                buf = Buf::new(len / 2);
                assert!(buf.len() == 0);
                
                runs.merge(r);
            }
            
        }
        
    }
    //debug_assert!(runs.len() == 1 && runs.index(0).start == 0 && runs.index(0).len == len);
}