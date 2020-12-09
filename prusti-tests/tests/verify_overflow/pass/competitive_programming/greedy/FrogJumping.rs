use prusti_contracts::*;

pub struct VecWrapperI32 {
    _ghost_size: usize,
    v: Vec<isize>,
}

impl VecWrapperI32 {
    #[trusted]
    #[pure]
    #[ensures (0 <= result)]
    pub fn len(&self) -> isize {
        self._ghost_size as isize
    }

    #[trusted]
    #[requires(size > 0)]
    #[ensures (result.len() == size)]
    #[ensures (forall(|i: isize| (0 <= i && i < result.len()) ==> result.lookup(i) == 0))]
    pub fn new(size: isize) -> Self {
        Self {
            _ghost_size: size as usize,
            v: vec![0; size as usize],
        }
    }

    #[trusted]
    #[pure]
    #[requires (0 <= index && index < self.len())]
    pub fn lookup(&self, index: isize) -> isize {
        self.v[index as usize]
    }

    #[trusted]
    #[requires(0 <= idx && idx < self.len())]
    #[ensures(self.len() == old(self.len()))]
    #[ensures(self.lookup(idx) == value)]
    #[ensures(forall(|i: isize|
        (0 <= i && i < self.len() && i != idx) ==>
        self.lookup(i) == old(self.lookup(i))))]
    pub fn set(&mut self, idx: isize, value: isize) -> () {
        self.v[idx as usize] = value
    }
}

#[pure]
#[ensures (result <= a && result <= b)]
#[ensures (result == a || result == b)]
fn min(a: isize, b: isize) -> isize {
    if a < b {
        a
    } else {
        b
    }
}

// Recursive Solution

#[pure]
#[requires(positions.len() >= 2 && positions.len() <= 100000)]
#[requires(idx >= 0 && idx < positions.len())]
#[requires(positions.lookup(0) == 0)]
#[requires(last_positions.len() == positions.len())]
#[requires(forall(|i: isize| (i >= 0 && i < positions.len() - 1) ==>
        (last_positions.lookup(i) > i && last_positions.lookup(i) <= last_positions.lookup(i + 1) &&
        last_positions.lookup(i) < positions.len())))]
#[requires(forall(|i: isize, j: isize| (i >= 0 && i < positions.len() - 1 && j > i && j < positions.len()) ==>
        (last_positions.lookup(i) <= last_positions.lookup(j))))]
#[requires(last_positions.lookup(positions.len() - 1) == positions.len() - 1)]
#[ensures(forall(|i: isize, j:  isize| (i >= idx && i < positions.len() - 1 && j > i && j < positions.len()) ==> solve_rec(positions, last_positions, i) >= solve_rec(positions, last_positions, j)))]
#[ensures(forall(|i: isize| (i >= idx && i < positions.len() - 1) ==> solve_rec(positions, last_positions, i) >= solve_rec(positions, last_positions, i + 1)))]
fn solve_rec(positions: &VecWrapperI32, last_positions: &VecWrapperI32, idx: isize) -> isize {
    if idx == positions.len() - 1 {
        0
    } else {
        helper(
            positions,
            last_positions,
            idx + 1,
            last_positions.lookup(idx),
        ) + 1
    }
}

#[pure]
#[requires(positions.len() >= 2 && positions.len() <= 100000)]
#[requires(idx >= 0 && idx < positions.len())]
#[requires(end >= idx && end < positions.len())]
#[requires(positions.lookup(0) == 0)]
#[requires(last_positions.len() == positions.len())]
#[requires(forall(|i: isize| (i >= 0 && i < positions.len() - 1) ==>  (last_positions.lookup(i) > i && last_positions.lookup(i) <= last_positions.lookup(i + 1) && last_positions.lookup(i) < positions.len())))]
#[requires(last_positions.lookup(positions.len() - 1) == positions.len() - 1)]
#[requires(forall(|i: isize, j: isize| (i >= 0 && i < positions.len() - 1 && j > i && j < positions.len()) ==>
        (last_positions.lookup(i) <= last_positions.lookup(j))))]
#[ensures (result == solve_rec(positions, last_positions, end))]
#[ensures (forall(|i: isize| (i >= idx && i <= end) ==> result <= solve_rec(positions,  last_positions, i)))]
fn helper(
    positions: &VecWrapperI32,
    last_positions: &VecWrapperI32,
    idx: isize,
    end: isize,
) -> isize {
    if idx == end {
        solve_rec(positions, last_positions, idx)
    } else {
        min(
            solve_rec(positions, last_positions, idx),
            helper(positions, last_positions, idx + 1, end),
        )
    }
}

// Greedy Soulution

#[requires(positions.len() >= 2 && positions.len() <= 100000)]
#[requires(positions.lookup(0) == 0)]
#[requires(forall(|i: isize| (i > 0 && i < positions.len()) ==> (positions.lookup(i) >= positions.lookup(i - 1))))]
#[requires(forall(|i: isize| (i > 0 && i < positions.len()) ==> (positions.lookup(i) - positions.lookup(i - 1) <= r)))]
fn frog_jumping_greedy(positions: &VecWrapperI32, r: isize) -> isize {
    let last_positions = last(positions, r);
    solve_greedy(positions, &last_positions, 0)
}

#[pure]
#[requires(positions.len() >= 2 && positions.len() <= 100000)]
#[requires(idx >= 0 && idx < positions.len())]
#[requires(positions.lookup(0) == 0)]
#[requires(last_positions.len() == positions.len())]
#[requires(forall(|i: isize| (i >= 0 && i < positions.len() - 1) ==>
        (last_positions.lookup(i) > i && last_positions.lookup(i) <= last_positions.lookup(i + 1) &&
        last_positions.lookup(i) < positions.len())))]
#[requires(forall(|i: isize, j: isize| (i >= 0 && i < positions.len() - 1 && j > i && j < positions.len()) ==>
        (last_positions.lookup(i) <= last_positions.lookup(j))))]
#[requires(last_positions.lookup(positions.len() - 1) == positions.len() - 1)]
#[ensures(result == solve_rec(positions, last_positions, idx))]
fn solve_greedy(positions: &VecWrapperI32, last_positions: &VecWrapperI32, idx: isize) -> isize {
    if idx == positions.len() - 1 {
        0
    } else {
        solve_greedy(positions, last_positions, last_positions.lookup(idx)) + 1
    }
}

#[trusted]
#[requires(positions.len() >= 2 && positions.len() <= 100000)]
#[requires(forall(|i: isize| (i > 0 && i < positions.len()) ==> (positions.lookup(i) >= positions.lookup(i - 1))))]
#[requires(forall(|i: isize| (i > 0 && i < positions.len()) ==> (positions.lookup(i) - positions.lookup(i - 1) <= r)))]
#[ensures(result.len() == positions.len())]
#[ensures(forall(|i: isize| (i >= 0 && i < positions.len() - 1) ==>
        (result.lookup(i) > i && result.lookup(i) <= result.lookup(i + 1) &&
        result.lookup(i) < positions.len())))]
#[ensures(forall(|i: isize, j: isize| (i >= 0 && i < positions.len() - 1 && j > i && j < positions.len()) ==>
        (result.lookup(i) <= result.lookup(j))))]
#[ensures(result.lookup(positions.len() - 1) == positions.len() - 1)]
fn last(positions: &VecWrapperI32, r: isize) -> VecWrapperI32 {
    let len = positions.len();
    let mut result = VecWrapperI32::new(len);
    result.set(positions.len() - 1, positions.len() - 1);
    let mut idx1 = positions.len() - 2;
    while idx1 >= 0 {
       let mut idx2 = idx1 + 1;
        while idx2 < positions.len() && positions.lookup(idx2) - positions.lookup(idx1) <= r {
            idx2 += 1;
        }
        result.set(idx1, idx2 - 1);
        idx1 -= 1;
    }
    result
}
