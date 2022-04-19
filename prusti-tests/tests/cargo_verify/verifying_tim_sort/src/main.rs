extern crate prusti_contracts;
use prusti_contracts::*;

use std::vec::Vec;

pub fn main() {
    let mut x : [i32; 50] = [5; 50];
    //merge_sort(&mut x);
}

fn insert_head(v: &mut [i32]) {
    /*
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
    */
}

struct Buf{
    v: Vec<i32>,
}

impl Buf {
    /*
    #[trusted]
    #[pure]
    #[ensures(result >= 0)]
    pub fn len(&self) -> usize {
        self.v.len()
    }

    #[trusted]
    #[pure]
    #[requires(0 <= index && index < self.len())]
    //#[ensures(self.len() == old(self).len())]
    pub fn index(&self, index: usize) -> i32 {
        self.v[index]
    }

    #[trusted]
    #[ensures(self.len() == old(self).len() + 1)]
    pub fn push(&mut self, value: i32) {
        self.v.push(value);
    }
    */
}

//#[requires(mid >= 0 && mid <= v.len() && buf.len() == 0)]
fn merge(v: &mut [i32], mid: usize, buf: &mut Buf) {
    /*
    let len = v.len();
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
        
        while left < mid {
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
    */
}

struct Runs{
    start: Vec<usize>,
    len: Vec<usize>,
    runs_sum: usize,
}

impl Runs {
    #[trusted]
    #[pure]
    #[ensures(result >= 0)]
    pub fn len(&self) -> usize {
        self.len.len()
    }
    
    #[requires(self.runs_sum + value <= usize::MAX)]
    #[ensures(self.runs_sum == old(self.runs_sum) + value)]
    #[ensures(self.runs_sum <= usize::MAX)]
    pub fn add_runs_sum(&mut self, value: usize) {
        self.runs_sum += value;
    }

    // #[pure]
    // #[trusted]
    // #[requires(0 <= index && index < self.len())]
    // pub fn index_start(&self, index: usize) -> usize {
    //     self.start[index]
    // }

    #[pure]
    #[trusted]
    #[requires(0 <= index && index < self.len())]
    pub fn index_len(&self, index: usize) -> usize {
        self.len[index]
    }

    #[trusted]
    #[requires(2 * new_len <= usize::MAX)]
    #[requires(2 * (self.runs_sum + new_len) <= usize::MAX)]
    #[ensures(self.len() == old(self.len()) + 1)]
    #[ensures(self.runs_sum == old(self.runs_sum) + new_len)]
    #[ensures(new_len <= self.runs_sum)]
    #[ensures(2 * (self.runs_sum) <= usize::MAX)]
    #[ensures(self.index_len(self.len() - 1) == new_len)]
    #[ensures(self.runs_sum == old(self.runs_sum) + self.index_len(self.len() - 1))]
    #[ensures(forall(|i: usize| (0 <= i && i < self.len() ==> 2 * self.index_len(i) <= usize::MAX)))]
    pub fn push(&mut self, new_start: usize, new_len: usize) {
        self.add_runs_sum(new_len);
        self.start.push(new_start);
        self.len.push(new_len);
    }


    // #[trusted]
    // #[requires(0 <= index && index < self.len() - 1)]
    // #[requires(new_len == self.index_len(index) + self.index_len(index + 1))]
    // #[ensures(self.index_len(index) == old(self.index_len(index)) + old(self.index_len(index + 1)))]
    // #[ensures(self.len() == old(self.len()) - 1)]
    // #[ensures(self.runs_sum == old(self.runs_sum))]
    // #[ensures(2 * (self.runs_sum) <= usize::MAX)]
    // #[requires(forall(|i: usize| (0 <= i && i < self.len() ==> 2 * self.index_len(i) <= usize::MAX)))]
    // pub fn merge(&mut self, index: usize, new_start: usize, new_len: usize) {
    //     self.start[index] = new_start;
    //     self.len[index] = new_len;
    //     self.start.remove(index + 1);
    //     self.len.remove(index + 1);
    // }
}

// #[requires(forall(|i: usize| (0 <= i && i < runs.len() ==> 2 * runs.index_len(i) <= usize::MAX)))]
// #[requires(2 * runs.runs_sum <= usize::MAX)]
// #[ensures(result == runs.len() || (runs.len() > 1 && result < runs.len() - 1))]
// fn collapse(runs: &Runs) -> usize {
//     let n = runs.len();
//     if n >= 2 {
//         assert!(n >= 2 && n <= runs.len());
//         if runs.index_start(n - 1) == 0 {
//             return n - 2;
//         } else if runs.index_len(n - 2) <= runs.index_len(n - 1) {
//             return n - 2;
//         } else if n >= 3 {
//             assert!(n >= 3 && n <= runs.len());
//             assert!(runs.index_len(n - 2) <= usize::MAX);
//             assert!(runs.runs_sum <= usize::MAX);
//             //assert!(runs.index_len(n - 2) + runs.index_len(n - 1) <= usize::MAX);
//             if runs.index_len(n - 3) <= runs.index_len(n - 2) + runs.index_len(n - 1) {
//                 if runs.index_len(n - 3) < runs.index_len(n - 1) {
//                     return n - 3;
//                 } else {
//                     return n - 2;
//                 }
//             } else if n >= 4 {
//                 assert!(n >= 4 && n <= runs.len());
//                 if runs.index_len(n - 4) <= runs.index_len(n - 3) + runs.index_len(n - 2) {
//                     if runs.index_len(n - 3) < runs.index_len(n - 1) {
//                         return n - 3;
//                     } else {
//                         return n - 2;
//                     }
//                 }
//             }
//         }
//     }
//     return n;
// }

#[requires(runs.len() == 0 && runs.runs_sum == 0)]
#[requires(2 * v.len() <= usize::MAX)]
fn merge_sort(v: &mut [i32], runs: &mut Runs) {
    const MAX_INSERTION: usize = 20;
    const MIN_RUN: usize = 10;

    if v.len() == 0 {
        return;
    }

    let len = v.len();
    //assert!(len == v.len());
    if len <= MAX_INSERTION {
        if len >= 2 {
            let mut i = len - 2;
            loop {
                body_invariant!(i >= 0);
                insert_head(&mut v[i..]);
                if i == 0 {
                    break;
                } else {
                    //assert!(i > 0);
                    i -= 1;
                }
            }
        }
        return;
    }
    
    let mut buf = Buf{v: Vec::with_capacity(len / 2)};
    //let mut runs = Runs{start: vec![], len:vec![], runs_sum: 0};
    let mut end = len;
    //assert!(end == v.len());
    assert!(v.len() >= 1);
    assert!(runs.runs_sum == 0);
    assert!(runs.len() == 0);
    
    let mut cur_runs_len = 0;
    while end > 0 {
        body_invariant!(end >= 1 && end <= v.len());
        body_invariant!(cur_runs_len == runs.runs_sum);
        body_invariant!(cur_runs_len == v.len() - end);
        body_invariant!(runs.runs_sum == v.len() - end);
        body_invariant!(forall(|i: usize| (0 <= i && i < runs.len() ==> 2 * runs.index_len(i) <= usize::MAX)));
        
        
        let mut start = end - 1;
        assert!(start < end);
        
        if start > 0 {
            start -= 1;
            assert!(start < end - 1);
            assert!(end <= v.len());
            assert!(start < v.len() - 1);
            if v[start + 1] < v[start] {
                while start > 0 {
                    body_invariant!(cur_runs_len == v.len() - end);
                    body_invariant!(start >= 1 && start < v.len() - 1 && start < end);
                    if !(v[start] < v[start - 1]) {
                        break;
                    }
                    start -= 1;
                }
                //v[start..end].reverse();
            } else {
                while start > 0 {
                    body_invariant!(cur_runs_len == v.len() - end);
                    body_invariant!(start >= 1 && start < v.len() - 1 && start < end);
                    if v[start] < v[start - 1] {
                        break;
                    }
                    start -= 1;
                }
            }
        }


        while start > 0 && end - start < MIN_RUN {
            body_invariant!(cur_runs_len == v.len() - end);
            body_invariant!(start >= 1 && end <= v.len() && start < end);
            start -= 1;
            insert_head(&mut v[start..end]);
        }
        
        
        assert!(cur_runs_len == runs.runs_sum);
        assert!(cur_runs_len == v.len() - end);
        assert!(runs.runs_sum == v.len() - end);
        
        let new_len = end - start;
        assert!(2 * new_len <= usize::MAX);

        assert!(cur_runs_len + new_len <= v.len());
        assert!(runs.runs_sum + new_len <= v.len());
        assert!(2 * (cur_runs_len + new_len) <= usize::MAX);
        assert!(2 * (runs.runs_sum + new_len) <= usize::MAX);
        
        cur_runs_len += new_len;
        runs.push(start, new_len);
        
        assert!(cur_runs_len == v.len() - start);

        end = start;

        assert!(cur_runs_len == runs.runs_sum);
        assert!(cur_runs_len == v.len() - end);
        assert!(runs.runs_sum == v.len() - end);
        assert!(2 * cur_runs_len <= usize::MAX);
        assert!(2 * runs.runs_sum <= usize::MAX);
        
        /*
        loop {
            body_invariant!(forall(|i: usize| (0 <= i && i < runs.len() ==> 2 * runs.index_len(i) <= usize::MAX)));
            //body_invariant!(2 * runs.runs_sum <= usize::MAX);

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
                
                /*
                merge(
                    &mut v[left_start..right_start + right_len],
                    left_len,
                    &mut buf,
                );
                */
                runs.merge(r, left_start, left_len + right_len);
                //is part of upper function runs.remove(r + 1);
            }
            
        }
        */
    }
    //debug_assert!(runs.len() == 1 && runs.index(0).start == 0 && runs.index(0).len == len);
}

#[trusted]
#[requires(2 * v.len() <= usize::MAX)]
fn start(v: &mut [i32]) {
    let mut runs = Runs{start: vec![], len:vec![], runs_sum: 0};
    merge_sort(v, &mut runs);
}