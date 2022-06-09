extern crate prusti_contracts;
use prusti_contracts::*;

use std::vec::Vec;

pub fn main() {
    let mut x : [i32; 50] = [5; 50];
    //merge_sort(&mut x);
    //println!("{:?}", x);
}

#[trusted]
#[requires(v.len() > 1)]
#[requires(start_index < end_index - 1)]
#[requires(end_index > 1 && end_index <= v.len())]
// #[requires(forall(|i: usize| i < v.len() ==> (v[i] == 0 || v[i] == 1)))]
#[requires(forall(|x: usize, y: usize| (start_index + 1 <= x && x <= y && y < end_index) ==> v[x] <= v[y]))]

#[ensures(v.len() == old(v.len()))]
// #[ensures(forall(|i: usize| i < v.len() ==> (v[i] == 0 || v[i] == 1)))]
// #[ensures(sum_zero(v, v.len()) == sum_zero(old(v), v.len()))]
#[ensures(forall(|x: usize, y: usize| (start_index <= x && x <= y && y < end_index) ==> v[x] <= v[y]))]
fn insert_head(v: &mut [i32], start_index: usize, end_index: usize) {
    let mut i = start_index + 1;
    while i < end_index {
        body_invariant!(i < end_index);
        body_invariant!(forall(|x: usize, y: usize| (start_index + 1 <= x && x <= y && y <= i) ==> v[x] <= v[y]));
        i += 1;
    }
    if v.len() >= 2 && (v[start_index + 1] < v[start_index]) {
        let tmp = v[start_index];
        v[start_index] = v[start_index + 1];
        let mut i = start_index + 2;
        assert!(v[start_index] <= v[start_index + 1]);
        assert!(tmp >= v[start_index]);
        assert!(tmp >= v[start_index + 1]);
        while i < end_index {
            body_invariant!(i >= start_index + 2 && i < end_index);
            body_invariant!(tmp >= v[i - 1]);
            body_invariant!(v[i - 2] == v[i - 1]);
            body_invariant!(forall(|x: usize, y: usize| (i <= x && x <= y && y < end_index) ==> v[x] <= v[y]));
            if v[i] >= tmp {
                assert!(tmp >= v[i - 2]);
                break;
            }
            v[i - 1] = v[i];
            assert!(tmp > v[i]);
            i += 1;
        }
        v[i - 1] = tmp;
        assert!(i == end_index || (tmp <= v[i] && tmp >= v[i - 2]));
    }
    let mut i = start_index;   
    while i < end_index {
        body_invariant!(i < end_index);
        body_invariant!(forall(|x: usize, y: usize| (start_index <= x && x <= y && y <= i) ==> v[x] <= v[y]));
        i += 1;
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

#[trusted]
#[requires(start < mid_full && mid_full < end && end <= v_full.len())]
#[requires(buf.len() == 0)]
#[requires(forall(|i: usize, j: usize| start <= i && i <= j && j < mid_full ==> v_full[i] <= v_full[j]))]
#[requires(forall(|i: usize, j: usize| mid_full <= i && i <= j && j < end ==> v_full[i] <= v_full[j]))]

#[requires(forall(|i: usize, x: usize, y: usize| (0 <= i && i < runs.len() && runs.index_start(i) <= x && x <= y && y < runs.index_start(i) + runs.index_len(i)) ==> v_full[x] <= v_full[y]))]

#[ensures(v_full.len() == old(v_full.len()))]
#[ensures(forall(|i: usize, j: usize| start <= i && i <= j && j < mid_full ==> v_full[i] <= v_full[j]))]
#[ensures(forall(|i: usize, j: usize| mid_full <= i && i <= j && j < end ==> v_full[i] <= v_full[j]))]
#[ensures(forall(|i: usize, j: usize| start <= i && i <= j && j < end ==> v_full[i] <= v_full[j]))]

#[ensures(forall(|i: usize, x: usize, y: usize| (0 <= i && i < runs.len() && runs.index_start(i) <= x && x <= y && y < runs.index_start(i) + runs.index_len(i)) ==> v_full[x] <= v_full[y]))]
fn merge(v_full: &mut [i32], start: usize, mid_full: usize, end: usize, buf: &mut Buf, runs: &Runs) {
    let v = &mut v_full[start..end];
    let mid = mid_full - start;
    //assert!(v.len() == end - start);
    //assert!(0 < mid_full - start && mid_full - start < v.len());
    // #[ensures(forall(|i: usize, j: usize| start <= i && i < end && j == i - start ==> v[i] == result[j]))]
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
            
            body_invariant!(forall(|x: usize, y: usize| 0 <= x && x <= y && y < out ==> v[x] <= v[y]));
            // body_invariant!(forall(|x: usize, y: usize| right <= x && x <= y && y < len ==> v[x] <= v[y]));

            if v[right] < buf.index(left) {
                v[out] = v[right];
                right += 1;
            } else {
                v[out] = buf.index(left);
                left += 1;
            }
            out += 1;
        }

        assert!(out == mid);
        assert!(v.len() == len);
        
        while left < mid {
            body_invariant!(v.len() == len);

            body_invariant!(left < mid);
            body_invariant!(v.len() - out >= mid - left);
            body_invariant!(out < v.len());
            
            body_invariant!(left < mid);
            body_invariant!(buf.len() == mid);
            body_invariant!(left < buf.len());

            body_invariant!(forall(|x: usize, y: usize| 0 <= x && x <= y && y < out ==> v[x] <= v[y]));
            // body_invariant!(forall(|x: usize, y: usize| right <= x && x <= y && y < len ==> v[x] <= v[y])); // we can remove this

            v[out] = buf.index(left);
            out += 1;
            left += 1;
        }

        assert!(out == right);
        
        let mut u = 0;
        while u < len {
            body_invariant!(forall(|x: usize, y: usize| 0 <= x && x <= y && y < u ==> v[x] <= v[y]));
            u += 1;
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

            // body_invariant!(forall(|x: usize, y: usize| 0 <= x && x <= y && y < left ==> v[x] <= v[y]));
            body_invariant!(forall(|x: usize, y: usize| out <= x && x <= y && y < len ==> v[x] <= v[y]));
            
            out -= 1;
            if buf.index(right - 1) < v[left - 1] {
                left -= 1;
                v[out] = v[left];
            } else {
                right -= 1;
                v[out] = buf.index(right);
            }
        }

        assert!(out == mid);
        assert!(v.len() == len);

        while right > 0 {
            body_invariant!(v.len() == len);

            body_invariant!(right >= 1);
           
            body_invariant!(right <= len - mid);
            body_invariant!(right <= buf.len());

            body_invariant!(right <= len);
            body_invariant!(right <= v.len());

            // body_invariant!(forall(|x: usize, y: usize| 0 <= x && x <= y && y < left ==> v[x] <= v[y])); // we can remove this
            // body_invariant!(forall(|x: usize, y: usize| out <= x && x <= y && y < len ==> v[x] <= v[y])); // we can remove this

            right -= 1;
            v[right] = buf.index(right);
        }

        assert!(out == left);
        
        let mut u = 0;
        while u < len {
            body_invariant!(forall(|x: usize, y: usize| 0 <= x && x <= y && y < u ==> v[x] <= v[y]));
            u += 1;
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
    #[requires(new_len > 0)]
    #[requires(self.get_runs_sum_max() == v.len())]
    #[requires(new_len + new_start <= self.get_runs_sum_max())]
    #[requires(forall(|i: usize| (0 <= i && i < self.len() ==> self.index_len(i) <= self.get_runs_sum_cur())))]
    #[requires(self.get_runs_sum_cur() + new_len <= self.get_runs_sum_max())]
    #[requires(forall(|i: usize| (0 <= i && i < self.len() ==> self.index_len(i) + new_len <= self.get_runs_sum_max())))]
    #[requires(forall(|i: usize, j: usize| (0 <= i && i < self.len() && i < j && j < self.len() ==> self.index_len(i) + self.index_len(j) <= self.get_runs_sum_max())))]
    #[requires(forall(|i: usize, j: usize| (self.len() < 2 || (self.len() >= 2 && 0 <= i && i < (self.len() - 1) && j == i + 1 ==> self.index_start(i) > self.index_start(j)))))]
    #[requires(self.len() == 0 || self.index_start(self.len() - 1) == self.get_runs_sum_max() - self.get_runs_sum_cur())]
    #[requires(self.len() == 0 || new_start < self.index_start(self.len() - 1))]
    #[requires(self.len() < 1 || new_start + new_len == self.index_start(self.len() - 1))]
    #[requires(self.len() < 2 || forall(|i: usize, j: usize| 0 <= i && i < (self.len() - 1) && j == i + 1 ==> self.index_start(j) + self.index_len(j) == self.index_start(i)))]
    #[requires(forall(|i: usize| (0 <= i && i < self.len() ==> self.index_len(i) + self.index_start(i) <= self.get_runs_sum_max())))]
    #[requires(forall(|i: usize| 0 <= i && i < self.len() ==> self.index_len(i) > 0))]

    #[requires(forall(|i: usize, j: usize| (new_start <= i && i <= j && j < new_start + new_len) ==> v[i] <= v[j]))]
    #[requires(forall(|i: usize, x: usize, y: usize| (0 <= i && i < self.len() && self.index_start(i) <= x && x <= y && y < self.index_start(i) + self.index_len(i)) ==> v[x] <= v[y]))]

    #[requires((self.len() == 0 && new_len + new_start == v.len()) || (self.len() > 0 && self.index_start(0) + self.index_len(0) == v.len()))]

    #[ensures(self.get_runs_sum_max() == v.len())]
    #[ensures(self.len() == old(self.len()) + 1)]
    #[ensures(self.index_len(self.len() - 1) == new_len)]
    #[ensures(self.get_runs_sum_cur() == new_len + old(self.get_runs_sum_cur()))]
    #[ensures(self.get_runs_sum_max() == old(self.get_runs_sum_max()))]
    #[ensures(forall(|i: usize| (0 <= i && i < self.len() ==> self.index_len(i) <= self.get_runs_sum_cur())))]
    #[ensures(forall(|i: usize, j: usize| (0 <= i && i < self.len() && i < j && j < self.len() ==> self.index_len(i) + self.index_len(j) <= self.get_runs_sum_max())))]
    #[ensures(self.len() < 2 || forall(|i: usize, j: usize| (0 <= i && i < (self.len() - 1) && j == i + 1 ==> self.index_start(i) > self.index_start(j))))]
    #[ensures(self.index_start(self.len() - 1) == self.get_runs_sum_max() - self.get_runs_sum_cur())]
    #[ensures(self.len() < 2 || forall(|i: usize, j: usize| 0 <= i && i < (self.len() - 1) && j == i + 1 ==> self.index_start(j) + self.index_len(j) == self.index_start(i)))]
    #[ensures(forall(|i: usize| (0 <= i && i < self.len() ==> self.index_len(i) + self.index_start(i) <= self.get_runs_sum_max())))]
    #[ensures(forall(|i: usize| 0 <= i && i < self.len() ==> self.index_len(i) > 0))]
    
    #[ensures(forall(|i: usize, x: usize, y: usize| (0 <= i && i < self.len() && self.index_start(i) <= x && x <= y && y < self.index_start(i) + self.index_len(i)) ==> v[x] <= v[y]))]
    
    #[ensures(self.index_start(0) + self.index_len(0) == v.len())]
    pub fn push(&mut self, new_start: usize, new_len: usize, v: &[i32]) {
        self.add_runs_sum_cur(new_len);
        self.start.push(new_start);
        self.len.push(new_len);
    }

    
    #[trusted]
    #[requires(self.get_runs_sum_max() == v.len())]
    #[requires(0 <= index && index < self.len() - 1)]
    #[requires(forall(|i: usize| (0 <= i && i < self.len() ==> self.index_len(i) <= self.get_runs_sum_cur())))]
    #[requires(forall(|i: usize, j: usize| (0 <= i && i < self.len() && i < j && j < self.len() ==> self.index_len(i) + self.index_len(j) <= self.get_runs_sum_max())))]
    #[requires(forall(|i: usize| (0 <= i && i < self.len() ==> self.index_len(i) + self.index_start(i) <= self.get_runs_sum_max())))]
    #[requires(self.len() < 2 || forall(|i: usize, j: usize| (0 <= i && i < (self.len() - 1) && j == i + 1 ==> self.index_start(i) > self.index_start(j))))]
    #[requires(self.index_start(self.len() - 1) == self.get_runs_sum_max() - self.get_runs_sum_cur())]
    #[requires(self.len() < 2 || forall(|i: usize, j: usize| 0 <= i && i < (self.len() - 1) && j == i + 1 ==> self.index_start(j) + self.index_len(j) == self.index_start(i)))]
    #[requires(forall(|i: usize| 0 <= i && i < self.len() ==> self.index_len(i) > 0))]

    #[requires(forall(|x: usize, y: usize| (self.index_start(index + 1) <= x && x <= y && y < self.index_start(index) + self.index_len(index)) ==> v[x] <= v[y]))]
    #[requires(forall(|i: usize, x: usize, y: usize| (0 <= i && i < self.len() && self.index_start(i) <= x && x <= y && y < self.index_start(i) + self.index_len(i)) ==> v[x] <= v[y]))]
    
    #[requires(self.index_start(0) + self.index_len(0) == v.len())]

    #[ensures(self.get_runs_sum_max() == v.len())]
    #[ensures(self.len() == old(self.len()) - 1)]
    #[ensures(self.index_len(index) == old(self.index_len(index)) + old(self.index_len(index + 1)))]
    #[ensures(self.index_start(index) == old(self.index_start(index + 1)))]
    #[ensures(self.get_runs_sum_cur() == old(self.get_runs_sum_cur()))]
    #[ensures(self.get_runs_sum_max() == old(self.get_runs_sum_max()))]
    #[ensures(forall(|i: usize| (0 <= i && i < self.len() ==> self.index_len(i) <= self.get_runs_sum_cur())))]
    #[ensures(forall(|i: usize, j: usize| (0 <= i && i < self.len() && i < j && j < self.len() ==> self.index_len(i) + self.index_len(j) <= self.get_runs_sum_max())))]
    #[ensures(forall(|i: usize| (0 <= i && i < self.len() ==> self.index_len(i) + self.index_start(i) <= self.get_runs_sum_max())))]
    #[ensures(self.len() < 2 || forall(|i: usize, j: usize| (0 <= i && i < (self.len() - 1) && j == i + 1 ==> self.index_start(i) > self.index_start(j))))]
    #[ensures(self.index_start(self.len() - 1) == self.get_runs_sum_max() - self.get_runs_sum_cur())]
    #[ensures(self.len() < 2 || forall(|i: usize, j: usize| 0 <= i && i < (self.len() - 1) && j == i + 1 ==> self.index_start(j) + self.index_len(j) == self.index_start(i)))]
    #[ensures(forall(|i: usize| 0 <= i && i < self.len() ==> self.index_len(i) > 0))]

    #[ensures(forall(|x: usize, y: usize| (self.index_start(index) <= x && x <= y && y < self.index_start(index) + self.index_len(index)) ==> v[x] <= v[y]))]
    #[ensures(forall(|i: usize, x: usize, y: usize| (0 <= i && i < self.len() && self.index_start(i) <= x && x <= y && y < self.index_start(i) + self.index_len(i)) ==> v[x] <= v[y]))]
    
    #[ensures(self.index_start(0) + self.index_len(0) == v.len())]
    pub fn merge(&mut self, index: usize, v: &[i32]) {
        let new_start = self.index_start(index + 1);
        let new_len = self.index_len(index) + self.index_len(index + 1);
        self.start[index] = new_start;
        self.len[index] = new_len;
        self.start.remove(index + 1);
        self.len.remove(index + 1);
    }
}

#[requires(forall(|i: usize, j: usize| (0 <= i && i < runs.len() && i < j && j < runs.len() ==> runs.index_len(i) + runs.index_len(j) <= runs.get_runs_sum_max())))]
#[ensures(result == runs.len() || (runs.len() > 1 && result < runs.len() - 1))]
#[ensures(runs.len() < 2 || (runs.index_start(runs.len() - 1) != 0 || result == runs.len() - 2))]
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

#[requires(v.len() >= 1 && v.len() <= usize::MAX)]
#[ensures(v.len() < 2 || forall(|x: usize, y: usize| 0 <= x && x <= y && y < v.len() ==> v[x] <= v[y]))]
fn sort_small_array(v: &mut [i32]) {
    if v.len() < 2 {
        return;
    } else {
        let len = v.len();
        let mut i = v.len() - 2;
        loop {
            body_invariant!(len == v.len());
            body_invariant!(i < v.len() - 1);
            body_invariant!(forall(|x: usize, y: usize| (i + 1 <= x && x <= y && y < v.len()) ==> v[x] <= v[y]));
            insert_head(v, i, len);
            if i == 0 {
                break;
            } else {
                i -= 1;
            }
        }   
    }
}


// the last pre and post conditions are not proved inside the function yet
#[trusted]
#[requires(v.len() <= usize::MAX)]
#[requires(runs.get_runs_sum_max() == v.len())]
#[requires(end >= 1 && end <= v.len())]
#[requires(runs.get_runs_sum_cur() == v.len() - end)]
#[requires(MIN_RUN < 100)]
#[requires(forall(|i: usize| (0 <= i && i < runs.len() ==> runs.index_len(i) <= runs.get_runs_sum_cur())))]
#[requires(forall(|i: usize, j: usize| (0 <= i && i < runs.len() && i < j && j < runs.len() ==> runs.index_len(i) + runs.index_len(j) <= runs.get_runs_sum_max())))]
#[requires(forall(|i: usize| (0 <= i && i < runs.len() ==> runs.index_len(i) + runs.index_start(i) <= runs.get_runs_sum_max())))]
#[requires(runs.len() < 2 || forall(|i: usize, j: usize| (0 <= i && i < (runs.len() - 1) && j == i + 1 ==> runs.index_start(i) > runs.index_start(j))))]
#[requires(runs.len() == 0 || runs.index_start(runs.len() - 1) == runs.get_runs_sum_max() - runs.get_runs_sum_cur())]
#[requires(runs.len() < 2 || forall(|i: usize, j: usize| (0 <= i && i < (runs.len() - 1) && j == i + 1 ==> runs.index_start(j) + runs.index_len(j) == runs.index_start(i))))]
#[requires(forall(|i: usize| 0 <= i && i < runs.len() ==> runs.index_len(i) > 0))]

#[requires(forall(|i: usize, x: usize, y: usize| (0 <= i && i < runs.len() && runs.index_start(i) <= x && x <= y && y < runs.index_start(i) + runs.index_len(i)) ==> v[x] <= v[y]))]

#[requires(runs.len() == 0 || runs.index_start(0) + runs.index_len(0) == v.len())]

#[ensures(runs.len() == old(runs.len()) + 1)]
#[ensures(runs.len() > 0)]
#[ensures(forall(|i: usize| (0 <= i && i < runs.len() ==> runs.index_len(i) <= runs.get_runs_sum_cur())))]
#[ensures(forall(|i: usize, j: usize| (0 <= i && i < runs.len() && i < j && j < runs.len() ==> runs.index_len(i) + runs.index_len(j) <= runs.get_runs_sum_max())))]
#[ensures(forall(|i: usize| (0 <= i && i < runs.len() ==> runs.index_len(i) + runs.index_start(i) <= runs.get_runs_sum_max())))]
#[ensures(runs.len() < 2 || forall(|i: usize, j: usize| (0 <= i && i < (runs.len() - 1) && j == i + 1 ==> runs.index_start(i) > runs.index_start(j))))]
#[ensures(runs.index_start(runs.len() - 1) == runs.get_runs_sum_max() - runs.get_runs_sum_cur())]
#[ensures(runs.len() < 2 || forall(|i: usize, j: usize| (0 <= i && i < (runs.len() - 1) && j == i + 1 ==> runs.index_start(j) + runs.index_len(j) == runs.index_start(i))))]
#[ensures(result >= 0 && result < v.len())]
#[ensures(v.len() == old(v.len()))]
#[ensures(runs.get_runs_sum_cur() == v.len() - result)]
#[ensures(runs.get_runs_sum_max() == old(runs.get_runs_sum_max()))]
#[ensures(runs.get_runs_sum_max() == v.len())]
#[ensures(forall(|i: usize| 0 <= i && i < runs.len() ==> runs.index_len(i) > 0))]

#[ensures(forall(|i: usize, x: usize, y: usize| (0 <= i && i < runs.len() && runs.index_start(i) <= x && x <= y && y < runs.index_start(i) + runs.index_len(i)) ==> v[x] <= v[y]))]

#[ensures(runs.index_start(0) + runs.index_len(0) == v.len())]
fn push_new_run(v: &mut [i32], runs: &mut Runs, mut end: usize, MIN_RUN: usize) -> usize {
    let mut start = end - 1;
    assert!(start < end);
    
    let mut u = 0;
    while u < runs.len() {
        body_invariant!(u < runs.len());
        body_invariant!(forall(|i: usize, x: usize, y: usize| (0 <= i && i < 0 && runs.index_len(i) <= x && x <= y && y <= runs.index_start(i) + runs.index_len(i)) ==> v[x] <= v[y]));
        u += 1;
    }

    if start > 0 {
        start -= 1;
        assert!(start < end - 1);
        assert!(end <= v.len());
        assert!(start < v.len() - 1);
        if v[start + 1] < v[start] {
            assert!(v[start] >= v[start + 1]);
            while start > 0 {
                body_invariant!(runs.get_runs_sum_cur() == v.len() - end);
                body_invariant!(start >= 1 && start < v.len() - 1 && start < end);
                body_invariant!(forall(|x: usize, y: usize| (start <= x && x <= y && y < end) ==> v[x] >= v[y]));
                if !(v[start] < v[start - 1]) {
                    break;
                }
                assert!(v[start - 1] >= v[start]);
                start -= 1;
                assert!(v[start] >= v[start + 1]);
            }
            let mut i = start;
            while i < end {
                body_invariant!(i < end);
                body_invariant!(forall(|x: usize, y: usize| (start <= x && x <= y && y <= i) ==> v[x] >= v[y]));
                i += 1;
            }
            v[start..end].reverse();
            let mut i = start;
            while i < end {
                body_invariant!(i < end);
                body_invariant!(forall(|x: usize, y: usize| (start <= x && x <= y && y <= i) ==> v[x] <= v[y]));
                i += 1;
            }
        } else {
            assert!(v[start] <= v[start + 1]);
            while start > 0 {
                body_invariant!(runs.get_runs_sum_cur() == v.len() - end);
                body_invariant!(start >= 1 && start < v.len() - 1 && start < end);
                body_invariant!(forall(|x: usize, y: usize| (start <= x && x <= y && y < end) ==> v[x] <= v[y]));
                if v[start] < v[start - 1] {
                    break;
                }
                assert!(v[start - 1] <= v[start]);
                start -= 1;
                assert!(v[start] <= v[start + 1]);
            }
            let mut i = start;
            while i < end {
                body_invariant!(i < end);
                body_invariant!(forall(|x: usize, y: usize| (start <= x && x <= y && y <= i) ==> v[x] <= v[y]));
                i += 1;
            }
        }
    }

    assert!(runs.get_runs_sum_cur() == v.len() - end);

    while start > 0 && end - start < MIN_RUN {
        body_invariant!(runs.get_runs_sum_cur() == v.len() - end);
        body_invariant!(start >= 1 && end <= v.len() && start < end);
        body_invariant!(forall(|x: usize, y: usize| (start <= x && x <= y && y < end) ==> v[x] <= v[y]));
        start -= 1;
        insert_head(v, start, end);
    }

    let mut i = start;
    while i < end {
        body_invariant!(i < end);
        body_invariant!(forall(|x: usize, y: usize| (start <= x && x <= y && y <= i) ==> v[x] >= v[y]));
        i += 1;
    }

    assert!(runs.get_runs_sum_cur() == v.len() - end);
    
    assert!(runs.len() == 0 || runs.index_start(runs.len() - 1) == runs.get_runs_sum_max() - runs.get_runs_sum_cur());
    assert!(runs.get_runs_sum_max() - runs.get_runs_sum_cur() == end);
    assert!(start < end);
    assert!(runs.len() == 0 || (runs.index_start(runs.len() - 1) == end && start < runs.index_start(runs.len() - 1)));

    let new_len = end - start;
    assert!(new_len > 0);
    assert!(start + new_len <= v.len());
    assert!(start + new_len <= runs.get_runs_sum_max());
    
    assert!(start + new_len == end);
    assert!(runs.len() == 0 || start + new_len == runs.index_start(runs.len() - 1));

    let mut i = start;
    while i < start + new_len {
        body_invariant!(i < start + new_len);
        body_invariant!(forall(|x: usize, y: usize| (start <= x && x <= y && y <= i) ==> v[x] >= v[y]));
        i += 1;
    }

    // assert!((runs.len() == 0 && end == v.len()) || (runs.len() > 0 && runs.index_start(0) + runs.index_len(0) == v.len()));

    runs.push(start, new_len, &v);
    
    assert!(runs.get_runs_sum_cur() == runs.get_runs_sum_max() - start);
    assert!(runs.get_runs_sum_max() == v.len());
    assert!(runs.get_runs_sum_cur() == v.len() - start);

    end = start;

    assert!(runs.get_runs_sum_cur() == v.len() - end);
    
    return end;
}


#[requires(v.len() <= usize::MAX)]
// #[ensures(forall(|x: usize, y: usize| ((0 <= x && x <= y && y < v.len()) ==> v[x] <= v[y])))]
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
        body_invariant!(runs.len() < 2 || forall(|i: usize, j: usize| (0 <= i && i < (runs.len() - 1) && j == i + 1 ==> runs.index_start(i) > runs.index_start(j))));
        body_invariant!(runs.len() == 0 || runs.index_start(runs.len() - 1) == runs.get_runs_sum_max() - runs.get_runs_sum_cur());
        body_invariant!(runs.len() < 2 || forall(|i: usize, j: usize| 0 <= i && i < (runs.len() - 1) && j == i + 1 ==> runs.index_start(j) + runs.index_len(j) == runs.index_start(i)));
        body_invariant!(forall(|i: usize| 0 <= i && i < runs.len() ==> runs.index_len(i) > 0));

        body_invariant!(forall(|i: usize, x: usize, y: usize| (0 <= i && i < runs.len() && runs.index_start(i) <= x && x <= y && y < runs.index_start(i) + runs.index_len(i)) ==> v[x] <= v[y]));

        body_invariant!(runs.len() == 0 || runs.index_start(runs.len() - 1) == end);

        body_invariant!(runs.len() == 0 || runs.index_start(0) + runs.index_len(0) == v.len());

        assert!(end >= 1 && end <= v.len());
        end = push_new_run(v, &mut runs, end, MIN_RUN_COPY);
        // assert!(runs.get_runs_sum_cur() == v.len() - end);
        // assert!(runs.get_runs_sum_max() == v.len());
        
        // assert!(runs.len() > 0);
        // assert!(runs.index_start(runs.len() - 1) == end);

        // assert!(runs.index_start(0) + runs.index_len(0) == v.len());
        
        // let length = runs.len();

        assert!(runs.len() > 0);

        loop {
            body_invariant!(runs.len() > 0);

            // body_invariant!(buf.len() == 0);
            // body_invariant!(runs.get_runs_sum_max() == v.len());
            // body_invariant!(runs.get_runs_sum_cur() == v.len() - end);
            // body_invariant!(runs.get_runs_sum_cur() <= runs.get_runs_sum_max());
            // body_invariant!(forall(|i: usize| (0 <= i && i < runs.len() ==> runs.index_len(i) <= runs.get_runs_sum_cur())));
            // body_invariant!(forall(|i: usize, j: usize| (0 <= i && i < runs.len() && i < j && j < runs.len() ==> runs.index_len(i) + runs.index_len(j) <= runs.get_runs_sum_max())));
            // body_invariant!(forall(|i: usize| (0 <= i && i < runs.len() ==> runs.index_len(i) + runs.index_start(i) <= runs.get_runs_sum_max())));
            // body_invariant!(runs.len() < 2 || forall(|i: usize, j: usize| (0 <= i && i < (runs.len() - 1) && j == i + 1 ==> runs.index_start(i) > runs.index_start(j))));
            // //edit here, remove runs.len() == 0 ???
            // body_invariant!(runs.len() == 0 || runs.index_start(runs.len() - 1) == runs.get_runs_sum_max() - runs.get_runs_sum_cur());
            // body_invariant!(runs.len() < 2 || forall(|i: usize, j: usize| 0 <= i && i < (runs.len() - 1) && j == i + 1 ==> runs.index_start(j) + runs.index_len(j) == runs.index_start(i)));
            // body_invariant!(forall(|i: usize| 0 <= i && i < runs.len() ==> runs.index_len(i) > 0));

            // body_invariant!(forall(|i: usize, x: usize, y: usize| (0 <= i && i < runs.len() && runs.index_start(i) <= x && x <= y && y < runs.index_start(i) + runs.index_len(i)) ==> v[x] <= v[y]));
            

            break;
            // body_invariant!(runs.index_start(runs.len() - 1) == end);

            // body_invariant!(runs.index_start(0) + runs.index_len(0) == v.len());
            
            // let r = collapse(&runs);
            // assert!(runs.len() > 0);
            
            // assert!(r == runs.len() || (runs.len() > 1 && r < runs.len() - 1));
            // assert!(runs.len() < 2 || (runs.index_start(runs.len() - 1) != 0 || r == runs.len() - 2));

            // assert!(runs.index_start(runs.len() - 1) != 0 || (runs.len() < 2 || r == runs.len() - 2));
            // // assert!(runs.index_start(runs.len() - 1) == end);
            // assert!(end != 0 || (runs.len() < 2 || r == runs.len() - 2));

            // if r == runs.len() {
            //     assert!(runs.len() > 0);
                
            //     assert!(runs.len() < 2 || (runs.index_start(runs.len() - 1) != 0 || r == runs.len() - 2));
            //     assert!(r == runs.len());
            //     // assert!(r != runs.len() - 2);
            //     assert!(runs.len() < 2 || runs.index_start(runs.len() - 1) != 0);

            // //     // assert!(end == 0);
            // //     // assert!(runs.index_start(runs.len() - 1) == end);
            // //     // assert!(runs.index_start(runs.len() - 1) == 0);
                
            // //     // assert!(runs.len() < 2);
            // //     // assert!(runs.len() == 1);

            //     break;
            // } else {
            //     break;
            // }
            //     assert!(runs.len() > 1 && r < runs.len() - 1);
            //     assert!(runs.len() > 1);

            //     let left_start = runs.index_start(r + 1);
            //     let left_len = runs.index_len(r + 1);
            //     let right_start = runs.index_start(r);
            //     let right_len = runs.index_len(r);
                
            //     // working
            //     assert!(left_start < right_start);
            //     assert!(right_start + right_len <= runs.get_runs_sum_max());
            //     assert!(right_start + right_len <= v.len());

            //     assert!(left_start + left_len == right_start);
                
            //     // not working
            //     assert!(right_len > 0);
            //     assert!(left_start + left_len < right_start + right_len);

            //     // merge requires
            //     // 1) v[left.start..left.start+left.len] is sorted
            //     // 2) v[right.start(=left.start+left.len)..right.start+right.len] is sorted
                
            //     merge(v, left_start, left_start + left_len, right_start + right_len, &mut buf, &runs);
                
            //     // merge ensures
            //     // 1) v[left.start..left.start+left.len] is sorted
            //     // 2) v[right.start(=left.start+left.len)..right.start+right.len] is sorted
            //     // 3) v[left.start..right.start+right.len] is sorted
                
            //     buf = Buf::new(len / 2);
            //     assert!(buf.len() == 0);
                
            //     // assert!(runs.len() > 1);
            //     runs.merge(r, &v);
            //     assert!(runs.len() > 0);
            // }
            // assert!(runs.len() > 0);
        }
        // assert!(runs.len() > 0);

        // assert!(end != 0 || runs.len() == 1);
    }

    assert!(runs.get_runs_sum_cur() == v.len());
    assert!(runs.get_runs_sum_cur() == runs.get_runs_sum_max());
    
    assert!(runs.len() > 0);
    // assert!(runs.len() == 1);
    assert!(runs.index_start(0) + runs.index_len(0) == v.len());

    assert!(end == 0);
    assert!(runs.index_start(runs.len() - 1) == end);
    assert!(runs.index_start(runs.len() - 1) == 0);

    //debug_assert!(runs.len() == 1 && runs.index(0).start == 0 && runs.index(0).len == len);
}

// Remaining things to prove
// 1) runs.index_start(runs.len() - 1) == end which will be 0 at the end
// 2) runs.len() == 0 || runs.index_start(0) + runs.index_len(0) == v.len() == runs.get_runs_sum_max()
// 3) at the end of the loop, runs.len() == 1
// follows ==> runs.index_start(0) == 0 && runs.index_start(0) + runs.index_len(0) == v.len() && that run is sorted