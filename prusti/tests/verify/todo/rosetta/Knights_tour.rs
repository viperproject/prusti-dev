//! An adaptation of the example from
//! https://rosettacode.org/wiki/Knight%27s_tour#Rust

extern crate prusti_contracts;

struct VecWrapperI32I32{
    v: Vec<(i32, i32)>
}

impl VecWrapperI32I32 {

    #[trusted]
    #[ensures="result.len() == 0"]
    pub fn new() -> Self {
        VecWrapperI32I32{ v: Vec::new() }
    }

    #[trusted]
    #[pure]
    #[ensures="result >= 0"]
    pub fn len(&self) -> usize {
        self.v.len()
    }

    #[trusted]
    #[requires="0 <= index && index < self.len()"]
    pub fn lookup(&self, index: usize) -> (i32, i32) {
        self.v[index]
    }
}

struct VecWrapperI32Point{
    v: Vec<(i32, Point)>
}

impl VecWrapperI32Point {

    #[trusted]
    #[ensures="result.len() == 0"]
    pub fn new() -> Self {
        VecWrapperI32Point{ v: Vec::new() }
    }

    #[trusted]
    #[pure]
    #[ensures="result >= 0"]
    pub fn len(&self) -> usize {
        self.v.len()
    }

    #[trusted]
    #[ensures="self.len() == old(self.len()) + 1"]
    pub fn push(&mut self, value: (i32, Point)) {
        self.v.push(value);
    }

    #[trusted]
    #[requires="0 <= index && index < self.len()"]
    pub fn lookup(&self, index: usize) -> (i32, Point) {
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
    #[requires="0 <= x && x < size()"]
    #[requires="0 <= y && y < size()"]
    fn lookup(&self, x: i32, y: i32) -> i32 {
        self.v[x as usize][y as usize]
    }

    #[trusted]
    #[requires="0 <= x && x < size()"]
    #[requires="0 <= y && y < size()"]
    #[ensures="self.lookup(x, y) == value"]
    #[ensures="forall px: i32, py: i32 ::
               (0 <= px && px < size() && px != x && 0 <= py && py < size() && py != y) ==>
               self.lookup(px, py) == old(self.lookup(px, py))"]
    pub fn store(&mut self, x: i32, y: i32, value: i32) {
        self.v[x as usize][y as usize] = value;
    }
}

use std::fmt;
 
const SIZE: usize = 8;

#[trusted]
#[pure]
#[ensures="result == 8"]
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
    fn mov(&mut self, &mut (dx,dy): &mut (i32, i32)) -> Point {
        Point {
            x: self.x + dx,
            y: self.y + dy
        }
    }
    fn clone(&mut self) -> Point {
        Point {
            x: self.x,
            y: self.y,
        }
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
 
    fn available(&self, p: Point) -> bool {
        let valid = 0 <= p.x && p.x < size()
                 && 0 <= p.y && p.y < size();
        return valid  && self.field.lookup(p.x, p.y) == 0;
    }
 
    // calculate the number of possible moves
    fn count_degree(&self, p: Point) -> i32 {
        let mut p = p;
        let mut count = 0;
        let moves = moves();
        let mut i = 0;
        let mut continue_loop = i < moves.len();
        while continue_loop {
            let mut dir = moves.lookup(i);  // TODO: Problematic line.
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
 
#[requires="0 <= x && x < size() && 0 <= y && y < size()"]
fn knights_tour(x: i32, y: i32) -> Option<Board> {
    let mut board = Board::new();
    let mut p = Point {x: x, y: y};
    let mut step = 1;
    let mut failed = false;
    board.field.store(p.x, p.y, step);
    step += 1;

    let mut continue_loop_1 = step <= size() * size();
 
    while continue_loop_1 {
        // choose next square by Warnsdorf's rule
        let mut candidates = VecWrapperI32Point::new();
        let moves = moves();
        let mut i = 0;
        let mut continue_loop = i < moves.len();
        while continue_loop {
            let mut dir = moves.lookup(i);  // TODO: Problematic line.
            let mut adj = p.mov(&mut dir);
            if board.available(adj.clone()) {
                let degree = board.count_degree(adj.clone());
                candidates.push((degree, adj));
            }
            i += 1;
            continue_loop = i < moves.len();
        }

        let mut i = 0;
        let mut continue_loop_2 = i < candidates.len();
        let mut min = None;
        let mut min_degree = size() * size();
        while continue_loop_2 {
            let (degree, adj) = candidates.lookup(i);  // TODO: Problematic line.
            if min_degree > degree {
                min_degree = degree;
                min = Some((degree, adj));
            }
            i += 1;
            continue_loop_2 = i < candidates.len();
        }
        match min {
            Some((_, adj)) => // move to next square
                p = adj,
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
