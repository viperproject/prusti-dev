//! An adaptation of the example from
//! https://rosettacode.org/wiki/Knight%27s_tour#Rust
//!
//! Changes:
//!
//! +   Inlined constants.
//! +   Unified types to remove type casts.
//! +   Rewrote loops into supported shape (while bool with no break, continue, or return).
//! +   Replaced comprehension with a manual loop.
//! +   Replaced ``println!`` with calling trusted functions.
//! +   Replaced auto-derives with manually written functions.
//!
//! Verified properties:
//!
//! +   Absence of panics.

use prusti_contracts::*;

struct VecWrapperI32I32{
    v: Vec<(i32, i32)>
}

impl VecWrapperI32I32 {

    #[trusted]
    #[ensures(result.len() == 0)]
    pub fn new() -> Self {
        VecWrapperI32I32{ v: Vec::new() }
    }

    #[trusted]
    #[pure]
    #[ensures(result >= 0)]
    pub fn len(&self) -> usize {
        self.v.len()
    }

    #[trusted]
    #[requires(0 <= index && index < self.len())]
    pub fn lookup(&mut self, index: usize) -> (i32, i32) {
        self.v[index]
    }
}

struct VecCandidates{
    v: Vec<(i32, Point)>
}

impl VecCandidates {

    #[trusted]
    #[ensures(result.len() == 0)]
    pub fn new() -> Self {
        VecCandidates{ v: Vec::new() }
    }

    #[trusted]
    #[pure]
    #[ensures(result >= 0)]
    pub fn len(&self) -> usize {
        self.v.len()
    }

    #[trusted]
    #[requires(0 <= value.1.x && value.1.x < size())]
    #[requires(0 <= value.1.y && value.1.y < size())]
    #[ensures(self.len() == old(self.len()) + 1)]
    pub fn push(&mut self, value: (i32, Point)) {
        self.v.push(value);
    }

    #[trusted]
    #[requires(0 <= index && index < self.len())]
    #[ensures(0 <= result.1.x && result.1.x < size())]
    #[ensures(0 <= result.1.y && result.1.y < size())]
    pub fn lookup(&mut self, index: usize) -> (i32, Point) {
        let r = &self.v[index];
        (r.0, Point { x: r.1.x, y: r.1.y })
    }
}

struct VecVecWrapperI32 {
    v: Vec<Vec<i32>>,
}

impl VecVecWrapperI32 {

    #[trusted]
    fn new() -> Self {
        Self {
            v: vec![vec![0;SIZE];SIZE],
        }
    }

    #[pure]
    #[trusted]
    #[requires(0 <= x && x < size())]
    #[requires(0 <= y && y < size())]
    fn lookup(&self, x: i32, y: i32) -> i32 {
        self.v[x as usize][y as usize]
    }

    #[trusted]
    #[requires(0 <= x && x < size())]
    #[requires(0 <= y && y < size())]
    #[ensures(self.lookup(x, y) == value)]
    #[ensures(forall px: i32, py: i32 ::
               (0 <= px && px < size() && px != x && 0 <= py && py < size() && py != y) ==>
               self.lookup(px, py) == old(self.lookup(px, py)))]
    pub fn store(&mut self, x: i32, y: i32, value: i32) {
        self.v[x as usize][y as usize] = value;
    }
}

use std::fmt;
 
const SIZE: usize = 8;

#[trusted]
#[pure]
#[ensures(result == 8)]
fn size() -> i32 {
    SIZE as i32
}

#[trusted]
fn moves() -> VecWrapperI32I32 {
    VecWrapperI32I32 {
        v: vec![(2,1), (1,2), (-1,2), (-2,1), (-2,-1), (-1,-2), (1,-2), (2,-1)],
    }
}
 
struct Point {
    x: i32,
    y: i32
}
 
impl Point {
    #[ensures(self.x == old(self.x))]
    #[ensures(self.y == old(self.y))]
    fn mov(&mut self, &mut (dx,dy): &mut (i32, i32)) -> Point {
        Point {
            x: self.x + dx,
            y: self.y + dy
        }
    }
    #[ensures(result.x == old(self.x))]
    #[ensures(result.y == old(self.y))]
    #[ensures(self.x == old(self.x))]
    #[ensures(self.y == old(self.y))]
    fn clone(&mut self) -> Point {
        Point {
            x: self.x,
            y: self.y,
        }
    }
}

#[pure]
fn valid(point: &Option<(i32, Point)>) -> bool {
    match point {
        Some((_, p)) => 0 <= p.x && p.x < size() && 0 <= p.y && p.y < size(),
        None => true,
    }
}
 
struct Board {
    field: VecVecWrapperI32,
}
 
impl Board {
 
    fn new() -> Board {
        return Board {
            field: VecVecWrapperI32::new(),
        };
    }
 
    #[ensures(result ==> (0 <= p.x && p.x < size() && 0 <= p.y && p.y < size()))]
    fn available(&mut self, p: Point) -> bool {
        let valid = 0 <= p.x && p.x < size()
                 && 0 <= p.y && p.y < size();
        return valid  && self.field.lookup(p.x, p.y) == 0;
    }
 
    // calculate the number of possible moves
    fn count_degree(&mut self, p: Point) -> i32 {
        let mut p = p;
        let mut count = 0;
        let mut moves = moves();
        let mut i = 0;
        let mut continue_loop = i < moves.len();
        while continue_loop {
            body_invariant!(0 <= i);
            body_invariant!(i < moves.len());
            let mut dir = moves.lookup(i);
            let next = p.mov(&mut dir);
            if self.available(next) {
                count += 1;
            }
            i += 1;
            continue_loop = i < moves.len();
        }
        return count;
    }
}
 
impl fmt::Display for Board {

    #[trusted]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for row in self.field.v.iter() {
            for x in row.iter(){
                try!(write!(f, "{:3} ", x));
            }
            try!(write!(f, "\n"));
        }
        Ok(())
    }
}
 
#[requires(0 <= x && x < size() && 0 <= y && y < size())]
fn knights_tour(x: i32, y: i32) -> Option<Board> {
    let mut board = Board::new();
    let mut p = Point {x: x, y: y};
    let mut step = 1;
    let mut failed = false;
    board.field.store(p.x, p.y, step);
    step += 1;

    let mut continue_loop_1 = step <= size() * size();
 
    while continue_loop_1 {
        body_invariant!(0 <= p.x && p.x < size());
        body_invariant!(0 <= p.y && p.y < size());
        // choose next square by Warnsdorf's rule
        let mut candidates = VecCandidates::new();
        let mut moves = moves();
        let mut i = 0;
        let mut continue_loop_3 = i < moves.len();
        while continue_loop_3 {
            body_invariant!(0 <= i);
            body_invariant!(i < moves.len());
            body_invariant!(0 <= p.x && p.x < size());
            body_invariant!(0 <= p.y && p.y < size());
            let mut dir = moves.lookup(i);
            let mut adj = p.mov(&mut dir);
            if board.available(adj.clone()) {
                let degree = board.count_degree(adj.clone());
                candidates.push((degree, adj));
            }
            i += 1;
            continue_loop_3 = i < moves.len();
        }

        let mut i = 0;
        let mut continue_loop_2 = i < candidates.len();
        let mut min = None;
        let mut min_degree = size() * size();
        while continue_loop_2 {
            body_invariant!(0 <= i);
            body_invariant!(i < candidates.len());
            body_invariant!(valid(&min));
            let (degree, adj) = candidates.lookup(i);
            if min_degree > degree {
                min_degree = degree;
                min = Some((degree, adj));
            }
            i += 1;
            continue_loop_2 = i < candidates.len();
        }
        match min {
            Some((_, adj)) => {// move to next square
                p = adj;
            }
            None =>            // can't move
                failed = true,
        };
        board.field.store(p.x, p.y, step);
        step += 1;
        continue_loop_1 = step <= size() * size() && !failed;
    }
    if failed {
        None
    } else {
        return Some(board);
    }
}

#[trusted]
fn print_board_size() {
    println!("Board size: {}", SIZE);
}

#[trusted]
fn print_starting_position(x: i32, y: i32) {
    println!("Starting position: ({}, {})", x, y);
}

#[trusted]
fn print_board(b: Board) {
    print!("{}", b);
}

#[trusted]
fn print_fail() {
    println!("Fail!")
}
 
fn main() {
    let (x, y) = (3, 1);
    print_board_size();
    print_starting_position(x, y);
    match knights_tour(x, y) {
        Some(b) =>
            print_board(b),
        None =>
            print_fail(),
    }
}
