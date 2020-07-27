//! An adaptation of the example from
//! https://rosettacode.org/wiki/Knight%27s_tour#Rust
//!
//! Changes:
//!
//! +   Inlined constants.
//! +   Unified types to remove type casts.
//! +   Introduced Moves and Candidates containers that store elements
//!     with specific invariants.
//! +   Rewrote loops into supported shape (while bool with no break,
//!     continue, or return).
//! +   Replaced comprehension with a manual loop.
//! +   Replaced ``println!`` with calling trusted functions.
//! +   Replaced auto-derives with manually written functions.
//!
//! Verified properties:
//!
//! +   Absence of panics.

// ignore-test Flaky test

extern crate prusti_contracts;

pub struct VecWrapper<T>{
    v: Vec<T>
}

impl<T> VecWrapper<T> {

    #[trusted]
    #[ensures="result.len() == 0"]
    pub fn new() -> Self {
        VecWrapper{ v: Vec::new() }
    }

    #[trusted]
    #[ensures="self.len() == old(self.len()) + 1"]
    pub fn push(&mut self, value: T) {
        self.v.push(value);
    }

    #[trusted]
    #[pure]
    pub fn len(&self) -> usize {
        self.v.len()
    }

    #[trusted]
    #[requires="0 <= index && index < self.len()"]
    pub fn index(&self, index: usize) -> &T {
        &self.v[index]
    }

    #[trusted]
    #[requires="0 <= index && index < self.len()"]
    #[ensures="after_expiry(self.len() == old(self.len()))"]
    pub fn index_mut(&mut self, index: usize) -> &mut T {
        &mut self.v[index]
    }
}

struct VecVecWrapper<T> {
    s: i32,
    v: Vec<Vec<T>>,
}

impl<T: Clone> VecVecWrapper<T> {

    #[trusted]
    #[requires="board_size >= 0"]
    #[ensures="result.size() == board_size"]
    fn new(board_size: i32, default_value: T) -> Self {
        Self {
            s: board_size,
            v: vec![vec![default_value;board_size as usize];board_size as usize],
        }
    }

    #[pure]
    pub fn size(&self) -> i32 {
        self.s
    }

    #[trusted]
    #[requires="0 <= index_x && index_x < self.size()"]
    #[requires="0 <= index_y && index_y < self.size()"]
    pub fn index(&self, index_x: i32, index_y: i32) -> &T {
        &self.v[index_x as usize][index_y as usize]
    }

    #[trusted]
    #[requires="0 <= index_x && index_x < self.size()"]
    #[requires="0 <= index_y && index_y < self.size()"]
    #[ensures="after_expiry(self.size() == old(self.size()))"]
    pub fn index_mut(&mut self, index_x: i32, index_y: i32) -> &mut T {
        &mut self.v[index_x as usize][index_y as usize]
    }
}
 
const SIZE: usize = 8;

#[trusted]
#[pure]
#[ensures="result == 8"]
fn size() -> i32 {
    SIZE as i32
}

pub struct Moves{
    v: Vec<(i32, i32)>
}

impl Moves {

    #[trusted]
    #[pure]
    #[ensures="result >= 0"]
    pub fn len(&self) -> i32 {
        self.v.len() as i32
    }

    #[trusted]
    #[requires="0 <= index && index < self.len()"]
    #[ensures="-2 <= result.0 && result.0 <= 2"]
    #[ensures="-2 <= result.1 && result.1 <= 2"]
    pub fn index(&self, index: i32) -> &(i32, i32) {
        &self.v[index as usize]
    }
}

#[trusted]
fn moves() -> Moves {
    Moves {
        v: vec![(2,1), (1,2), (-1,2), (-2,1), (-2,-1), (-1,-2), (1,-2), (2,-1)],
    }
}

struct Candidates{
    v: Vec<(i32, Point)>
}

impl Candidates {

    #[trusted]
    #[ensures="result.len() == 0"]
    pub fn new() -> Self {
        Self { v: Vec::new() }
    }

    #[trusted]
    #[pure]
    #[ensures="result >= 0"]
    pub fn len(&self) -> usize {
        self.v.len()
    }

    #[trusted]
    #[requires="0 <= value.1.x && value.1.x < size()"]
    #[requires="0 <= value.1.y && value.1.y < size()"]
    #[ensures="self.len() == old(self.len()) + 1"]
    pub fn push(&mut self, value: (i32, Point)) {
        self.v.push(value);
    }

    #[trusted]
    #[requires="0 <= index && index < self.len()"]
    #[ensures="0 <= result.1.x && result.1.x < size()"]
    #[ensures="0 <= result.1.y && result.1.y < size()"]
    pub fn index(&self, index: usize) -> &(i32, Point) {
        &self.v[index]
    }
}

#[derive(Copy, Clone, Eq, PartialEq)]
struct Point {
    x: i32,
    y: i32
}

impl Point {
    #[requires="0 <= self.x && self.x < size()"]
    #[requires="0 <= self.y && self.y < size()"]
    #[requires="-2 <= dx && dx <= 2"]
    #[requires="-2 <= dy && dy <= 2"]
    fn mov(&self, &(dx,dy): &(i32, i32)) -> Point {
        Point {
            x: self.x + dx,
            y: self.y + dy
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
    field: VecVecWrapper<i32>,
}

impl Board {
 
    #[ensures="result.field.size() == size()"]
    fn new() -> Board {
        return Board {
            field: VecVecWrapper::new(size(), 0),
        };
    }
 
    #[requires="self.field.size() == size()"]
    #[ensures="result ==> (0 <= p.x && p.x < size() && 0 <= p.y && p.y < size())"]
    fn available(&self, p: Point) -> bool {
        let valid = 0 <= p.x && p.x < size()
                 && 0 <= p.y && p.y < size();
        return valid && *self.field.index(p.x, p.y) == 0;
    }
 
    // calculate the number of possible moves
    #[requires="self.field.size() == size()"]
    #[requires="0 <= p.x && p.x < size()"]
    #[requires="0 <= p.y && p.y < size()"]
    fn count_degree(&self, p: Point) -> i32 {
        let mut p = p;
        let mut count = 0;
        let mut moves = moves();
        let mut i = 0;
        let mut continue_loop = i < moves.len();
        #[invariant="self.field.size() == size()"]
        #[invariant="0 <= i"]
        #[invariant="continue_loop ==> i < moves.len()"]
        #[invariant="0 <= p.x && p.x < size()"]
        #[invariant="0 <= p.y && p.y < size()"]
        #[invariant="0 <= count && count <= i"]
        while continue_loop {
            let mut dir = moves.index(i);
            let next = p.mov(dir);
            if self.available(next) {
                count += 1;
            }
            i += 1;
            continue_loop = i < moves.len();
        }
        return count;
    }
}

#[requires="0 <= x && x < size() && 0 <= y && y < size()"]
fn knights_tour(x: i32, y: i32) -> Option<Board> {
    let mut board = Board::new();
    let mut p = Point {x: x, y: y};
    let mut step = 1;
    let mut failed = false;
    let board_cell = board.field.index_mut(p.x, p.y);
    *board_cell = step;
    step += 1;

    let mut continue_loop_1 = step <= size() * size();
 
    #[invariant="board.field.size() == size()"]
    #[invariant="0 <= p.x && p.x < size()"]
    #[invariant="0 <= p.y && p.y < size()"]
    #[invariant="continue_loop_1 ==> step <= size() * size()"]
    while continue_loop_1 {
        // choose next square by Warnsdorf's rule
        let mut candidates = Candidates::new();
        let mut moves = moves();
        let mut i = 0;
        let mut continue_loop_3 = i < moves.len();
        #[invariant="board.field.size() == size()"]
        #[invariant="0 <= i"]
        #[invariant="continue_loop_3 ==> i < moves.len()"]
        #[invariant="0 <= p.x && p.x < size()"]
        #[invariant="0 <= p.y && p.y < size()"]
        while continue_loop_3 {
            let mut dir = moves.index(i);
            let mut adj = p.mov(dir);
            if board.available(adj) {
                let degree = board.count_degree(adj);
                candidates.push((degree, adj));
            }
            i += 1;
            continue_loop_3 = i < moves.len();
        }

        let mut i = 0;
        let mut continue_loop_2 = i < candidates.len();
        let mut min = None;
        let mut min_degree = size() * size();
        #[invariant="0 <= i"]
        #[invariant="continue_loop_2 ==> i < candidates.len()"]
        #[invariant="valid(&min)"]
        while continue_loop_2 {
            let &(degree, adj) = candidates.index(i);
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
            // None
            _ =>            // can't move
                failed = true,
        };
        let board_cell = board.field.index_mut(p.x, p.y);
        *board_cell = step;
        step += 1;
        continue_loop_1 = step <= size() * size() && !failed;
    }
    if failed {
        None
    } else {
        return Some(board);
    }
}

use std::fmt;
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
 
pub fn test() {
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

fn main() {}
