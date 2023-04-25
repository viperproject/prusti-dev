// compile-flags: -Pviper_backend=Lithium
use prusti_contracts::*;

pub struct VecWrapperI32 {
    v: Vec<i32>,
}

impl VecWrapperI32 {
    #[trusted]
    #[pure]
    #[terminates]
    #[ensures (0 <= result)]
    pub fn len(&self) -> usize {
        self.v.len()
    }

    #[trusted]
    #[ensures (result.len() == 0)]
    pub fn new() -> Self {
        VecWrapperI32 { v: Vec::new() }
    }

    #[pure]
    #[terminates]
    #[trusted]
    #[requires (0 <= index)]
    #[requires (index < self.len())]
    pub fn lookup(&self, index: usize) -> i32 {
        self.v[index]
    }

    #[trusted]
    #[ensures (self.len() == old(self.len()) + 1)]
    #[ensures (self.lookup(old(self.len())) == value)]
    #[ensures (forall(|i: usize| (0 <= i && i < old(self.len())) ==>
                    self.lookup(i) == old(self.lookup(i))))]
    pub fn push(&mut self, value: i32) {
        self.v.push(value);
    }
}

#[pure]
#[terminates]
#[ensures (result >= a && result >= b)]
#[ensures (result == a || result == b)]
fn max(a: i32, b: i32) -> i32 {
    if a < b {
        b
    } else {
        a
    }
}

//  Recursive solution

#[pure]
#[terminates(Int::new_usize(i))]
#[requires(i >= 0)]
#[ensures(result >= 0)]
fn to_i32(i: usize) -> i32 {
    if i == 0 {
        0
    } else {
        1 + to_i32(i - 1)
    }
}

#[pure]
#[terminates(Int::new_usize(i))]
#[requires (i >= 0)]
#[requires (i < seq.len())]
#[requires (seq.len() > 0)]
#[requires (forall(|k: usize| (k >= 0 && k < seq.len()) ==> (seq.lookup(k) >= -1000 && seq.lookup(k) <= 1000)))]
#[requires (seq.len() <= 10000)]
#[ensures(result  >=  -1000)]
#[ensures(result  <=  (to_i32(i) + 1)  * 10000)]
fn max_seq_sum_rec(seq: &VecWrapperI32, i: usize) -> i32 {
    if i == 0 {
        seq.lookup(0)
    } else {
        let prev = max_seq_sum_rec(seq, i - 1);
        if prev > 0 {
            prev + seq.lookup(i)
        } else {
            seq.lookup(i)
        }
    }
}

#[pure]
#[terminates(Int::new_usize(idx))]
#[requires (seq.len() > 0)]
#[requires (idx >= 0)]
#[requires (idx < seq.len())]
#[requires (forall(|k: usize| (k >= 0 && k < seq.len()) ==> (seq.lookup(k) >= -1000 && seq.lookup(k) <= 1000)))]
#[requires (seq.len() <= 10000)]
fn solve_rec(seq: &VecWrapperI32, idx: usize) -> i32 {
    if idx == 0 {
        max_seq_sum_rec(seq, idx)
    } else {
        max(max_seq_sum_rec(seq, idx), solve_rec(seq, idx - 1))
    }
}

#[pure]
#[terminates]
#[requires (seq.len() > 0)]
#[requires (forall(|k: usize| (k >= 0 && k < seq.len()) ==> (seq.lookup(k) >= -1000 && seq.lookup(k) <= 1000)))]
#[requires (seq.len() <= 10000)]
fn the_jackpot_rec(seq: &VecWrapperI32) -> i32 {
    max(0, solve_rec(seq, seq.len() - 1))
}

// Naive Solution

#[pure]
#[terminates(Int::new_usize(end))]
#[requires (seq.len() > 0)]
#[requires (start >= 0)]
#[requires (start <=  end)]
#[requires (end < seq.len())]
#[requires (forall(|k: usize| (k >= 0 && k < seq.len()) ==> (seq.lookup(k) >= -1000 && seq.lookup(k) <= 1000)))]
#[requires (seq.len() <= 10000)]
#[ensures (result <=  max_seq_sum_rec(seq, end))]
#[ensures(result  >=  (to_i32(end - start + 1))  * -10000)]
#[ensures(result  <=  (to_i32(end - start + 1))  * 10000)]
fn seq_sum(seq: &VecWrapperI32, start: usize, end: usize) -> i32 {
    if end == start {
        seq.lookup(end)
    } else {
        seq.lookup(end) + seq_sum(seq, start, end - 1)
    }
}

#[pure]
#[terminates]
#[requires (a >= b)]
#[ensures (result == a - b)]
fn sub(a: usize, b: usize) -> usize {
    a - b
}

#[requires (seq.len() > 0)]
#[requires (start >= 0)]
#[requires (start <=  end)]
#[requires (end < seq.len())]
#[requires (forall(|k: usize| (k >= 0 && k < seq.len()) ==> (seq.lookup(k) >= -1000 && seq.lookup(k) <= 1000)))]
#[requires (seq.len() <= 10000)]
#[ensures (result <= solve_rec(seq, end))]
fn max_seq_sum(seq: &VecWrapperI32, start: usize, end: usize) -> i32 {
    if start == end {
        seq_sum(seq, start, end)
    } else {
        max(max_seq_sum(seq, start + 1, end), seq_sum(seq, start, end))
    }
}

#[requires (seq.len() > 0)]
#[requires (end >= 0)]
#[requires (end < seq.len())]
#[requires (forall(|k: usize| (k >= 0 && k < seq.len()) ==> (seq.lookup(k) >= -1000 && seq.lookup(k) <= 1000)))]
#[requires (seq.len() <= 10000)]
#[ensures (result <= solve_rec(seq, end))]
fn solve_naive(seq: &VecWrapperI32, end: usize) -> i32 {
    if end == 0 {
        max_seq_sum(seq, 0, end)
    } else {
        max(solve_naive(seq, end - 1), max_seq_sum(seq, 0, end))
    }
}

#[requires (seq.len() > 0)]
#[requires (forall(|k: usize| (k >= 0 && k < seq.len()) ==> (seq.lookup(k) >= -1000 && seq.lookup(k) <= 1000)))]
#[requires (seq.len() <= 10000)]
#[ensures (result <= the_jackpot_rec(seq))]
fn the_jackpot_naive(seq: &VecWrapperI32) -> i32 {
    max(0, solve_naive(seq, seq.len() - 1))
}

// Solution >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

#[requires (seq.len() > 0)]
#[requires (forall(|k: usize| (k >= 0 && k < seq.len()) ==> (seq.lookup(k) >= -1000 && seq.lookup(k) <= 1000)))]
#[requires (seq.len() <= 10000)]
#[ensures (result.len() == seq.len())]
#[ensures (forall(|k:usize| (k >= 0 && k < seq.len()) ==> (result.lookup(k) == max_seq_sum_rec(seq, k))))]
fn solve(seq: &VecWrapperI32) -> VecWrapperI32 {
    let mut dp = VecWrapperI32::new();
    dp.push(seq.lookup(0));
    let mut i = 1usize;
    let len = seq.len();
    while i < len {
        body_invariant!(i >= 1);
        body_invariant!(i < seq.len());
        body_invariant!(dp.len() == i);
        body_invariant!(forall(|k: usize| (k < i && k >= 0) ==> dp.lookup(k) == max_seq_sum_rec(seq, k)));
        body_invariant!(forall(|k: usize| (k < i && k >= 0) ==> dp.lookup(k) <=  ((k + 1) as i32) * 10000));
        let prev = dp.lookup(i - 1);
        if prev > 0 {
            dp.push(prev + seq.lookup(i));
        } else {
            dp.push(seq.lookup(i));
        }
        i += 1;
    }
    dp
}

#[requires (seq.len() > 0)]
#[requires (forall(|k: usize| (k >= 0 && k < seq.len()) ==> (seq.lookup(k) >= -1000 && seq.lookup(k) <= 1000)))]
#[requires (seq.len() <= 10000)]
#[ensures (result == the_jackpot_rec(seq))]
fn the_jackpot(seq: &VecWrapperI32) -> i32 {
    let dp = solve(seq);
    let mut answer = seq.lookup(0);
    let len = seq.len();
    let mut idx = 1;
    while idx < len {
        body_invariant!(idx >= 1);
        body_invariant!(idx < len);
        body_invariant!(answer == solve_rec(seq, idx - 1));
        answer = max(answer, dp.lookup(idx));
        idx += 1;
    }
    assert!(answer == solve_rec(seq, seq.len() - 1));
    max(0, answer)
}

pub fn main() {}
