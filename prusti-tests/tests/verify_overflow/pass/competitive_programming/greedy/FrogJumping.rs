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
#[requires (a >= 0 && a < 100000)]
#[requires (b >= 0 && b < 100000)]
#[ensures (result <= a && result <= b)]
#[ensures (result == a || result == b)]
#[ensures (result >= 0 && result < 100000)]
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
#[requires(next > idx && next <= positions.len())]
#[requires(last_positions.len() == positions.len())]
#[requires(idx < positions.len() - 1 ==> next <= last_positions.lookup(idx))]
#[requires(positions.lookup(0) == 0)]
#[requires(forall(|i: isize| (i >= 0 && i < positions.len() - 1) ==>  (last_positions.lookup(i) > i && last_positions.lookup(i) <= last_positions.lookup(i + 1) && last_positions.lookup(i) < positions.len())))]
#[requires(last_positions.lookup(positions.len() - 1) == positions.len() - 1)]
#[requires(forall(|i: isize, j: isize| (i >= 0 && i < positions.len() - 1 && j > i && j < positions.len()) ==>
            (last_positions.lookup(i) <= last_positions.lookup(j))))]
#[ensures(result < positions.len() - idx && result < 100000 && result >= 0)]
#[ensures(result < positions.len() - idx && result < 100000 && result >= 0)]
#[ensures (forall(|i: isize| (i > next && i <= last_positions.lookup(idx)) ==> 
            result <= solve_rec(positions,  last_positions, idx, i)))]
#[ensures((idx < positions.len() - 1 && next == last_positions.lookup(idx)) ==> 
            result == solve_rec(positions, last_positions, next, next + 1) + 1)]
#[ensures((idx < positions.len() - 1 && next == idx + 1) ==> 
            result >= solve_rec(positions, last_positions, next, next + 1))]
#[ensures(next == idx + 1 ==> forall(|j:  isize| (j > idx && j < positions.len()) ==> 
            result >= solve_rec(positions, last_positions, j, j + 1)))]
#[ensures(idx < positions.len() - 1 ==> result == solve_rec(positions, last_positions, idx, last_positions.lookup(idx)))]
#[ensures(idx < positions.len() - 1 ==> 
            result == solve_rec(positions, last_positions, last_positions.lookup(idx), last_positions.lookup(idx) + 1) + 1)]
fn solve_rec(
    positions: &VecWrapperI32,
    last_positions: &VecWrapperI32,
    idx: isize,
    next: isize,
) -> isize {
    if idx == positions.len() - 1 {
        0
    } else if next == last_positions.lookup(idx) {
        assert!(idx < positions.len() - 1 && next == last_positions.lookup(idx));
        solve_rec(positions, last_positions, next, next + 1) + 1
    } else {
        assert!(idx < positions.len() - 1 && next < last_positions.lookup(idx));
        let take = solve_rec(positions, last_positions, next, next + 1) + 1;
        let leave = solve_rec(positions, last_positions, idx, next + 1);
        let x1 = last_positions.lookup(idx) + 1;
        let tmp1  = solve_rec(positions, last_positions, last_positions.lookup(idx), x1);
        assert!(leave ==  tmp1 + 1);
        let x2 = next + 1;
        assert!(x2 ==  next + 1);
        assert!(last_positions.lookup(idx) >  next && last_positions.lookup(idx) < positions.len());
        let tmp2 = solve_rec(positions, last_positions, next, x2);
        assert!(tmp2 >= tmp1);
        min(take, leave)
    }
}