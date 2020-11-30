// https://onlinejudge.org/external/12/1213.pdf
use prusti_contracts::*;

pub struct VecWrapperI32 {
    v: Vec<isize>,
}

impl VecWrapperI32 {
    #[trusted]
    #[pure]
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
    #[requires (0 <= index as usize && index < self.len())]
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
    #[trusted]
    #[ensures(0 < result)]
    fn x_size(&self) -> isize {
        self._ghost_x_size as isize
    }

    #[pure]
    #[trusted]
    #[ensures(0 < result)]
    fn y_size(&self) -> isize {
        self._ghost_y_size as isize
    }

    #[trusted]
    #[requires(0 <= y && y < self.y_size())]
    #[requires(0 <= x && x < self.x_size())]
    #[ensures(*result == old(self.lookup(y, x)))]
    #[after_expiry(
        self.y_size() == old(self.y_size()) &&
        self.x_size() == old(self.x_size()) &&
        self.lookup(y, x) == before_expiry(*result) &&
        forall(|i: isize, j: isize|
            (0 <= i && i < self.y_size() &&
             0 <= j && j < self.x_size() && !(j == x && i == y)) ==>
            self.lookup(i, j) == old(self.lookup(i, j)))
            && forall(|i: isize, j: isize|
                (i >= 0 && i < y && j >= 0 && j < self.x_size()) ==> (self.lookup(i, j) == old(self.lookup(i, j))))
    )]
    fn index_mut(&mut self, y: isize, x: isize) -> &mut isize {
        &mut self.vec[y as usize][x as usize]
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
    #[trusted]
    #[requires(0 <= y && y < self.y_size())]
    #[requires(0 <= x && x < self.x_size())]
    fn lookup(&self, y: isize, x: isize) -> isize {
        self.vec[y as usize][x as usize]
    }
}

#[pure]
#[requires(n <= 1120)]
#[requires(k <= 14)]
#[requires(primes.len() > 0)]
#[requires(forall(|k: isize| (k >= 0 && k < primes.len()) ==> (primes.lookup(k) >= 2)))]
#[ensures(k > 0 && n >= 0 ==> result  == sum_of_different_primes_rec_helper(primes, n, k, primes.len() - 1))]
fn sum_of_different_primes_rec(primes: &VecWrapperI32, n: isize, k: isize) -> isize {
    if k == 0 && n == 0 {
        1
    } else if (k <= 0 || n < 0) {
        0
    } else {
        sum_of_different_primes_rec_helper(primes, n, k, primes.len() - 1)
    }
}

#[requires(n <= 1120)]
#[requires(k <= 14)]
#[requires(primes.len() > 0)]
#[requires(forall(|k: isize| (k >= 0 && k < primes.len()) ==> (primes.lookup(k) >= 2)))]
#[ensures((k > 0 && n >= 0) ==> result == sum_of_different_primes_rec_helper(primes, n, k, primes.len() - 1))]
#[ensures(result == sum_of_different_primes_rec(primes, n, k))]
fn sum_of_different_primes_rec_iter(primes: &VecWrapperI32, n: isize, k: isize) -> isize {
    if k == 0 && n == 0 {
        1
    } else if (k <= 0 || n < 0) {
        0
    } else {
        let mut idx = 0isize;
        let mut answer = 0;
        while idx < primes.len() {
            body_invariant!(idx >= 0 && idx < primes.len());
            body_invariant!(n >= 0);
            body_invariant!(answer == sum_of_different_primes_rec_helper(primes, n, k, idx - 1));
            answer += sum_of_different_primes_rec(primes, n - primes.lookup(idx), k - 1);
            idx += 1;
        }
        answer
    }
}

#[pure]
#[requires(n >= 0 && n <= 1120)]
#[requires(k > 0 && k <= 14)]
#[requires(idx_prime >= -1 && idx_prime < primes.len())]
#[requires(primes.len() > 0)]
#[requires(forall(|k: isize| (k >= 0 && k < primes.len()) ==> (primes.lookup(k) >= 2)))]
fn sum_of_different_primes_rec_helper(
    primes: &VecWrapperI32,
    n: isize,
    k: isize,
    idx_prime: isize,
) -> isize {
    if idx_prime == -1{
        0
    } else {
        sum_of_different_primes_rec_helper(primes, n, k, idx_prime - 1)
            + sum_of_different_primes_rec(primes, n - primes.lookup(idx_prime), k - 1)
    }
}



#[requires(n > 0 && n <= 1120)]
#[requires(k > 0 && k <= 14)]
#[requires(primes.len() > 0)]
#[requires(forall(|k: isize| (k >= 0 && k < primes.len()) ==> (primes.lookup(k) >= 2 && primes.lookup(k) <= n)))]
fn sum_of_different_primes(primes: &VecWrapperI32, n: isize, k: isize) -> isize {
    let size_k = k + 1;
    let size_n = n + 1;
    let mut dp = Matrix::new(size_k, size_n);
    let mut idx_k = 1isize;
    let primes_len = primes.len();
    dp.set(0, 0, 1);
    while idx_k < size_k {
        body_invariant!(idx_k >= 0 && idx_k < size_k);
        body_invariant!(dp.y_size() == size_k && dp.x_size() == size_n);
        body_invariant!(idx_k > 0);
        body_invariant!(forall(|i: isize, j: isize| (i >= 0 && i < idx_k && j >= 0 && j < size_n) ==>  dp.lookup(i, j) == sum_of_different_primes_rec(primes, j, i)));
        body_invariant!(forall(|i: isize| (i >= 0 && i < size_n) ==>  dp.lookup(idx_k, i) == 0));
        let mut idx_n = 0isize;
        while idx_n < size_n {
            body_invariant!(idx_n >= 0 && idx_n < size_n);
            body_invariant!(dp.y_size() == size_k && dp.x_size() == size_n);
            body_invariant!(forall(|i: isize, j: isize| (i >= 0 && i < idx_k && j >= 0 && j < size_n) ==>  dp.lookup(i, j) == sum_of_different_primes_rec(primes, j, i)));
            body_invariant!(forall(|i: isize| (i >= 0 && i < idx_n) ==>  dp.lookup(idx_k, i) == sum_of_different_primes_rec(primes, i, idx_k)));
            
            dp.set(idx_k, idx_n, sum_of_different_primes_rec(primes, idx_n, idx_k)); 
            idx_n += 1;
        }
        idx_k += 1;
    }
    dp.lookup(k, n)
}

fn  main() {

}
