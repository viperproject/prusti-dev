// compile-flags: -Pviper_backend=Lithium
use prusti_contracts::*;

pub struct VecWrapperI32 {
    v: Vec<isize>,
}

impl VecWrapperI32 {
    #[trusted]
    #[pure]
    #[terminates]
    #[ensures (0 <= result)]
    pub fn len(&self) -> isize {
        self.v.len() as isize
    }

    #[trusted]
    #[ensures (result.len() == 0)]
    pub fn new() -> Self {
        VecWrapperI32 { v: Vec::new() }
    }

    #[trusted]
    #[pure]
    #[terminates]
    #[requires (0 <= index && index < self.len())]
    pub fn lookup(&self, index: isize) -> isize {
        self.v[index as usize]
    }

    #[trusted]
    #[ensures (self.len() == old(self.len()) + 1)]
    #[ensures (self.lookup(old(self.len())) == value)]
    #[ensures (forall(|i: isize| (0 <= i && i < old(self.len())) ==>
                    self.lookup(i) == old(self.lookup(i))))]
    pub fn push(&mut self, value: isize) {
        self.v.push(value);
    }
}

#[pure]
#[terminates]
#[ensures (result >= a && result >= b)]
#[ensures (result == a || result == b)]
fn max(a: isize, b: isize) -> isize {
    if a < b {
        b
    } else {
        a
    }
}

struct Matrix {
    _ghost_y_size: usize,
    _ghost_x_size: usize,
    vec: Vec<Vec<isize>>,
}

impl Matrix {
    #[trusted]
    #[requires(0 < y_size)]
    #[requires(0 < x_size)]
    #[ensures(result.y_size() == y_size)]
    #[ensures(result.x_size() == x_size)]
    #[ensures(forall(|y: isize, x: isize|
                (0 <= x && x < result.x_size() && 0 <= y && y < result.y_size()) ==>
                result.lookup(y, x) == 0))]
    fn new(y_size: isize, x_size: isize) -> Self {
        Self {
            _ghost_y_size: y_size as usize,
            _ghost_x_size: x_size as usize,
            vec: vec![vec![0; y_size as usize]; x_size as usize],
        }
    }

    #[pure]
    #[terminates]
    #[trusted]
    #[ensures(0 < result)]
    fn x_size(&self) -> isize {
        self._ghost_x_size as isize
    }

    #[pure]
    #[terminates]
    #[trusted]
    #[ensures(0 < result)]
    fn y_size(&self) -> isize {
        self._ghost_y_size as isize
    }

    #[trusted]
    #[requires(0 <= y && y < self.y_size())]
    #[requires(0 <= x && x < self.x_size())]
    #[ensures(self.y_size() == old(self.y_size()))]
    #[ensures(self.x_size() == old(self.x_size()))]
    #[ensures(forall(|i: isize, j: isize|
        (i >= 0 && i < y && j >= 0 && j < self.x_size()) ==> (self.lookup(i, j) == old(self.lookup(i, j)))))]
    #[ensures(self.lookup(y, x) == value)]
    #[ensures(forall(|i: isize, j: isize|
        (0 <= i && i < self.y_size() &&
         0 <= j && j < self.x_size() && !(j == x && i == y)) ==>
        self.lookup(i, j) == old(self.lookup(i, j))))]
    fn set(&mut self, y: isize, x: isize, value: isize) -> () {
        self.vec[y as usize][x as usize] = value
    }

    #[pure]
    #[terminates]
    #[trusted]
    #[requires(0 <= y && y < self.y_size())]
    #[requires(0 <= x && x < self.x_size())]
    fn lookup(&self, y: isize, x: isize) -> isize {
        self.vec[y as usize][x as usize]
    }
}

// Recursive solution

#[pure]
#[terminates(trusted)]
#[requires(prices.len() ==  weights.len())]
#[requires(prices.len() > 0 &&  weights.len() <= 1000)]
#[requires(index < prices.len() && index >= -1)]
#[requires(forall(|k: isize| (k >= 0 && k < prices.len()) ==>  prices.lookup(k) >= 1 && prices.lookup(k) <= 1000))]
#[requires(forall(|k: isize| (k >= 0 && k < weights.len()) ==>  weights.lookup(k) >= 1 && weights.lookup(k) <= 30))]
#[ensures(result <= (index + 1) *  1000)]
#[ensures(result >= 0)]
fn solve_rec(
    prices: &VecWrapperI32,
    weights: &VecWrapperI32,
    index: isize,
    remaining_weight: isize,
) -> isize {
    if remaining_weight <= 0 || index < 0 {
        0
    } else {
        assert!(index >= 0);
        if weights.lookup(index) <= remaining_weight {
            max(
                solve_rec(prices, weights, index - 1, remaining_weight),
                prices.lookup(index)
                    + solve_rec(
                        prices,
                        weights,
                        index - 1,
                        remaining_weight - weights.lookup(index),
                    ),
            )
        } else {
            solve_rec(prices, weights, index - 1, remaining_weight)
        }
    }
}

// // DP solution

#[requires(prices.len() ==  weights.len())]
#[requires(prices.len() > 0 &&  weights.len() <= 1000)]
#[requires(forall(|k: isize| (k >= 0 && k < prices.len()) ==>  prices.lookup(k) >= 1 && prices.lookup(k) <= 1000))]
#[requires(forall(|k: isize| (k >= 0 && k < weights.len()) ==>  weights.lookup(k) >= 1 && weights.lookup(k) <= 30))]
#[requires(dp.y_size() == 31 && dp.x_size() == prices.len())]
#[requires(index_weight >= 1 && index_weight < dp.y_size())]
#[requires(index_object >= 0 && index_object < dp.x_size())]
#[requires(forall(|i: isize, j: isize| (i >= 0 && i < index_weight && j >= 0 && j < dp.x_size()) ==> dp.lookup(i, j) == solve_rec(prices, weights, j, i)))]
#[requires(forall(|i: isize| (i >= 0 && i < index_object) ==> dp.lookup(index_weight, i) == solve_rec(prices, weights, i, index_weight)))]
#[ensures(result == solve_rec(prices, weights, index_object, index_weight))]
#[ensures(forall(|i: isize, j: isize| (i >= 0 && i < index_weight && j >= 0 && j < dp.x_size()) ==> dp.lookup(i, j) == solve_rec(prices, weights, j, i)))]
#[ensures(forall(|i: isize| (i >= 0 && i < index_object) ==> dp.lookup(index_weight, i) == solve_rec(prices, weights, i, index_weight)))]
fn helper(
    prices: &VecWrapperI32,
    weights: &VecWrapperI32,
    index_weight: isize,
    index_object: isize,
    dp: &Matrix,
) -> isize {
    let mut answer = 0;
    let index_before = index_object - 1;
    if index_before == -1 {
        if index_weight >= weights.lookup(index_object) {
            answer = prices.lookup(index_object);
        } else {
            answer = 0;
        }
    } else {
        if index_weight >= weights.lookup(index_object) {
            let remaining_weight = index_weight - weights.lookup(index_object);
            assert!(
                dp.lookup(remaining_weight, index_object - 1)
                    == solve_rec(prices, weights, index_object - 1, remaining_weight)
            );
            assert!(dp.lookup(remaining_weight, index_object - 1) <= index_object * 1000);
            answer = max(
                dp.lookup(index_weight, index_object - 1),
                prices.lookup(index_object) + dp.lookup(remaining_weight, index_object - 1),
            );
        } else {
            answer = dp.lookup(index_weight, index_object - 1);
        }
    }
    answer
}

#[trusted] // TODO: remove trusted
#[requires(prices.len() ==  weights.len())]
#[requires(prices.len() > 0 &&  weights.len() <= 1000)]
#[requires(forall(|k: isize| (k >= 0 && k < prices.len()) ==>  prices.lookup(k) >= 1 && prices.lookup(k) <= 1000))]
#[requires(forall(|k: isize| (k >= 0 && k < weights.len()) ==>  weights.lookup(k) >= 1 && weights.lookup(k) <= 30))]
#[requires(dp.y_size() == 31 && dp.x_size() == prices.len())]
#[requires(index_weight >= 1 && index_weight < dp.y_size())]
#[requires(forall(|i: isize, j: isize| (i >= 0 && i < index_weight && j >= 0 && j < dp.x_size()) ==>  dp.lookup(i, j) == solve_rec(prices, weights, j, i)))]
#[ensures(dp.y_size() == old(dp.y_size()))]
#[ensures(dp.x_size() == old(dp.x_size()))]
#[ensures(forall(|i: isize, j: isize| (i >= 0 && i <= index_weight && j >= 0 && j < dp.x_size()) ==>  dp.lookup(i, j) == solve_rec(prices, weights, j, i)))]
fn helper_loop(
    prices: &VecWrapperI32,
    weights: &VecWrapperI32,
    index_weight: isize,
    dp: &mut Matrix,
) {
    let mut index_object = 0isize;
    let n = prices.len();
    while index_object < dp.x_size() {
        body_invariant!(index_weight >= 1 && index_weight < dp.y_size());
        body_invariant!(index_object >= 0 && index_object < dp.x_size());
        body_invariant!(dp.y_size() == 31 && dp.x_size() == prices.len());
        body_invariant!(forall(|i: isize, j: isize| (i >= 0 && i < index_weight && j >= 0 && j < dp.x_size()) ==>  dp.lookup(i, j) == solve_rec(prices, weights, j, i)));
        body_invariant!(forall(|i: isize| (i >= 0 && i < index_object) ==> dp.lookup(index_weight, i) == solve_rec(prices, weights, i, index_weight)));
        let answer = helper(prices, weights, index_weight, index_object, &dp);
        dp.set(index_weight, index_object, answer);
        index_object += 1;
    }
}

#[requires(prices.len() ==  weights.len())]
#[requires(prices.len() > 0 &&  weights.len() <= 1000)]
#[requires(forall(|k: isize| (k >= 0 && k < prices.len()) ==>  prices.lookup(k) >= 1 && prices.lookup(k) <= 1000))]
#[requires(forall(|k: isize| (k >= 0 && k < weights.len()) ==>  weights.lookup(k) >= 1 && weights.lookup(k) <= 30))]
#[requires(forall(|k: isize| (k >= 0 && k < max_weights.len()) ==>  max_weights.lookup(k) >= 1 && max_weights.lookup(k) <= 30))]
#[ensures(result.len() == max_weights.len())]
#[ensures(forall(|k: isize| (k >= 0 && k < result.len()) ==>  result.lookup(k) == solve_rec(prices, weights, prices.len() -  1, max_weights.lookup(k))))]
fn super_sale(
    prices: &VecWrapperI32,
    weights: &VecWrapperI32,
    max_weights: &VecWrapperI32,
) -> VecWrapperI32 {
    let mut answer = VecWrapperI32::new();
    let g = max_weights.len();
    let n = prices.len();
    let max_weight = 31;
    let mut dp = Matrix::new(max_weight, n);
    let mut index_weight = 1isize;
    while index_weight <= 30 {
        body_invariant!(dp.y_size() == max_weight && dp.x_size() == n);
        body_invariant!(index_weight >= 1 && index_weight < max_weight);
        body_invariant!(forall(|i: isize, j: isize| (i >= 0 && i < index_weight && j >= 0 && j < dp.x_size()) ==> dp.lookup(i, j) == solve_rec(prices, weights, j, i)));
        helper_loop(prices, weights, index_weight, &mut dp);
        prusti_assume!(dp.y_size() == max_weight && dp.x_size() == n); // TODO: Postcondition should handle this
        index_weight += 1;
        prusti_assume!(forall(|i: isize, j: isize| (i >= 0 && i < index_weight && j >= 0 && j < dp.x_size()) ==> dp.lookup(i, j) == solve_rec(prices, weights, j, i)));
        // TODO: Postcondition should handle this
    }

    let mut index_person = 0isize;
    while index_person < g {
        body_invariant!(index_person >= 0 && index_person < g);
        body_invariant!(answer.len() == index_person);
        body_invariant!(forall(|k: isize| (k >= 0 && k < g) ==>  max_weights.lookup(k) >= 1 && max_weights.lookup(k) <= 30));
        body_invariant!(forall(|k: isize| (k >= 0 && k < index_person) ==>  answer.lookup(k) == solve_rec(prices, weights, prices.len() -  1, max_weights.lookup(k))));
        let w = max_weights.lookup(index_person);
        let cur_answer = dp.lookup(w, n - 1);
        answer.push(cur_answer);
        index_person += 1;
    }
    answer
}

fn main() {}
