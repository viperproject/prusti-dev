use prusti_contracts::*;

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
    #[ensures(self.lookup(y, x) == value)]
    #[ensures(forall(|i: isize, j: isize|
        (i >= 0 && i < y && j >= 0 && j < self.x_size()) ==> (self.lookup(i, j) == old(self.lookup(i, j)))))]
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
fn sum(l: isize) -> isize {
    l +  5
}

#[requires(n > 0 && n <= 1120)]
#[requires(k > 0 && k <= 14)]
#[ensures(result == sum(n - 1))]
fn test(n: isize, k: isize, l: isize)  -> isize{
    let mut dp = Matrix::new(k, n);

    let mut idx1 = 0isize;   

    while idx1 < k {
        body_invariant!(idx1 >= 0 && idx1 < k);
        body_invariant!(dp.y_size() == k && dp.x_size() == n);
        body_invariant!(forall(|i: isize, j: isize| (i >= 0 && i < idx1 && j >= 0 && j < n) ==>  dp.lookup(i, j) == sum(j)));
        let  mut idx2 = 0isize;
        let mut ans = sum(0);
        let mut idx3 = 0isize;
        while idx2 < n {
            body_invariant!(idx2 >= 0 && idx2 < n);
            body_invariant!(idx1 >= 0 && idx1 < k);
            body_invariant!(dp.y_size() == k && dp.x_size() == n);
            body_invariant!(forall(|i: isize, j: isize| (i >= 0 && i < idx1 && j >= 0 && j < n) ==>  dp.lookup(i, j) == sum(j)));
            body_invariant!(forall(|j: isize| (j >= 0 && j < idx2) ==>  dp.lookup(idx1, j) == sum(j)));
            dp.set(idx1, idx2, sum(idx2));
            idx2 += 1;
        }
        idx1 += 1;
    }
    dp.lookup(k  -  1, n -  1)
}