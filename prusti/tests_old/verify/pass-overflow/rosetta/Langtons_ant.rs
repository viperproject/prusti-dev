//! An adaptation of the example from
//! https://rosettacode.org/wiki/Langton%27s_ant#Rust
//!
//! Changes:
//!
//! +   Wrapped built-in types and functions.
//! +   Rewrote loops into supported shape (while bool with no break, continue, or return).
//! +   Replaced ``println!`` with calling trusted functions.
//! +   Added ghost functions to track the program state.
//! +   Fixed the bug by changing usize into isize.
//!
//! Verified properties (for fixed version):
//!
//! +   Absence of panics.
//! +   Absence of overflows.
//! +   Grid is always in a valid state: contains only 0s and 1s.
//!
//! Found bug:
//!
//! +   The subtraction may overflow because usize variable is used.

extern crate prusti_contracts;

struct Ant {
    x: isize,
    y: isize,
    dir: Direction
}
 
enum Direction {
    North,
    East,
    South,
    West
}
 
use Direction::*;

struct Matrix {
    _ghost_y_size: usize,
    _ghost_x_size: usize,
    vec: Vec<Vec<u8>>,
}

impl Matrix {

    #[trusted]
    #[requires="0 < y_size"]
    #[requires="0 < x_size"]
    #[ensures="result.y_size() == y_size"]
    #[ensures="result.x_size() == x_size"]
    #[ensures="forall y: isize, x: isize ::
                (0 <= x && x < result.x_size() && 0 <= y && y < result.y_size()) ==>
                result.lookup(y, x) == 0"]
    fn new(y_size: isize, x_size: isize) -> Self {
        Self {
            _ghost_y_size: y_size as usize,
            _ghost_x_size: x_size as usize,
            vec: vec![vec![0; y_size as usize]; x_size as usize],
        }
    }

    #[pure]
    #[trusted]
    #[ensures="0 < result"]
    fn x_size(&self) -> isize {
        self._ghost_x_size as isize
    }

    #[pure]
    #[trusted]
    #[ensures="0 < result"]
    fn y_size(&self) -> isize {
        self._ghost_y_size as isize
    }

    #[trusted]
    #[requires="0 <= y && y < self.y_size()"]
    #[requires="0 <= x && x < self.x_size()"]
    #[ensures="*result == old(self.lookup(y, x))"]
    #[ensures="after_expiry(
        self.y_size() == old(self.y_size()) &&
        self.x_size() == old(self.x_size()) &&
        self.lookup(y, x) == before_expiry(*result) &&
        (
            forall i: isize, j: isize ::
            (0 <= i && i < self.y_size() &&
             0 <= j && j < self.x_size() && !(j == x && i == y)) ==>
            self.lookup(i, j) == old(self.lookup(i, j))
        )
        )"]
    fn index_mut(&mut self, y: isize, x: isize) -> &mut u8 {
        &mut self.vec[y as usize][x as usize]
    }

    #[pure]
    #[trusted]
    #[requires="0 <= y && y < self.y_size()"]
    #[requires="0 <= x && x < self.x_size()"]
    fn lookup(&self, y: isize, x: isize) -> u8 {
        self.vec[y as usize][x as usize]
    }

}

#[trusted]
#[ensures="(a == 0 && b == 1) ==> result == 1"]
#[ensures="(a == 1 && b == 1) ==> result == 0"]
fn xor(a: u8, b: u8) -> u8 {
    a ^ b
}
 
impl Ant {
    #[pure]
    #[requires="y_size >= 0"]
    #[requires="x_size >= 0"]
    fn valid(&self, y_size: isize, x_size: isize) -> bool {
        0 <= self.y && self.y < y_size &&
        0 <= self.x && self.x < x_size
    }

    #[requires="self.valid(vec.y_size(), vec.x_size())"]
    #[requires="forall y: isize, x: isize ::
                (0 <= x && x < vec.x_size() && 0 <= y && y < vec.y_size()) ==>
                (vec.lookup(y, x) == 0 || vec.lookup(y, x) == 1)"]
    #[ensures="forall y: isize, x: isize ::
                (0 <= x && x < vec.x_size() && 0 <= y && y < vec.y_size()) ==>
                (vec.lookup(y, x) == 0 || vec.lookup(y, x) == 1)"]
    #[ensures="vec.y_size() == old(vec.y_size())"]
    #[ensures="vec.x_size() == old(vec.x_size())"]
    fn mv(&mut self, vec: &mut Matrix) {
        let pointer = vec.index_mut(self.y, self.x);
        //change direction
        match *pointer {
            0 => self.dir = self.dir.clone().right(),
            1 => self.dir = self.dir.clone().left(),
            _ => panic!("Unexpected colour in grid")
        }
        //flip colour
        //if it's 1 it's black
        //if it's 0 it's white
        *pointer = xor(*pointer, 1);

        //move direction
        match self.dir {
            North => self.y -= 1,
            South => self.y += 1,
            East => self.x += 1,
            West => self.x -= 1,
        }
 
    }
}


impl Direction {
    fn right(self) -> Direction {
        match self {
            North => East,
            East => South,
            South => West,
            West => North,
        }
    }
 
    fn left(self) -> Direction {
        //3 rights equal a left
        self.right().right().right()
    }

    fn clone(&mut self) -> Direction {
        match self {
            North => East,
            East => South,
            South => West,
            West => North,
        }
    }
}

#[trusted]
fn print_grid(grid: &mut Matrix) {
    for each in grid.vec.iter() {
        //construct string
        //using iterator methods to quickly convert the vector
        //to a string
        let string = each.iter()
                         .map(|&x| if x == 0 { " " } else { "#" })
                         .fold(String::new(), |x, y| x+y);
        println!("{}", string);
    }
}
 
fn main(){
    //create a 100x100 grid using vectors
    let mut grid = Matrix::new(100, 100);
    let mut ant = Ant {
        x: 50, y: 50, dir: Direction::North
    };

    let mut continue_loop = 0 <= ant.x && ant.x < 100 && 0 <= ant.y && ant.y < 100;
 
    #[invariant="grid.y_size() == 100"]
    #[invariant="grid.x_size() == 100"]
    #[invariant="ant.valid(grid.y_size(), grid.x_size())"]
    #[invariant="forall y: isize, x: isize ::
                (0 <= x && x < grid.x_size() && 0 <= y && y < grid.y_size()) ==>
                (grid.lookup(y, x) == 0 || grid.lookup(y, x) == 1)"]
    while continue_loop {
        ant.mv(&mut grid);
        continue_loop = 0 <= ant.x && ant.x < 100 && 0 <= ant.y && ant.y < 100;
        if continue_loop {
            assert!(ant.valid(grid.y_size(), grid.x_size()));
        }
    }
    print_grid(&mut grid);
}
