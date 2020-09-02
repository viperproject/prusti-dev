/// An adaptation of the example from
/// https://rosettacode.org/wiki/Langton%27s_ant#Rust
///
/// The part of the original Langton's Ant example that has an overflow error.

extern crate prusti_contracts;

struct Ant {
    x: usize,
    y: usize,
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
    #[ensures="result.y_size() == y_size"]
    #[ensures="result.x_size() == x_size"]
    #[ensures="forall y: usize, x: usize ::
                (0 <= x && x < result.x_size() && 0 <= y && y < result.y_size()) ==>
                result.lookup(y, x) == 0 || result.lookup(y, x) == 1"]
    fn new(y_size: usize, x_size: usize) -> Self {
        Self {
            _ghost_y_size: y_size,
            _ghost_x_size: x_size,
            vec: vec![vec![0; y_size]; x_size],
        }
    }

    #[pure]
    #[trusted]
    #[ensures="0 <= result"]
    fn x_size(&self) -> usize {
        self._ghost_x_size
    }

    #[pure]
    #[trusted]
    #[ensures="0 <= result"]
    fn y_size(&self) -> usize {
        self._ghost_y_size
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
            forall i: usize, j: usize ::
            (0 <= i && i < self.y_size() && i != y &&
             0 <= j && j < self.x_size() && j != x) ==>
            self.lookup(i, j) == old(self.lookup(i, j))
        )
        )"]
    fn borrow(&mut self, y: usize, x: usize) -> &mut u8 {
        &mut self.vec[y][x]
    }

    #[pure]
    #[trusted]
    #[requires="0 <= y && y < self.y_size()"]
    #[requires="0 <= x && x < self.x_size()"]
    fn lookup(&self, y: usize, x: usize) -> u8 {
        self.vec[y][x]
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
    fn valid(&self, y_size: usize, x_size: usize) -> bool {
        0 <= self.y && self.y < y_size &&
        0 <= self.x && self.x < x_size
    }

    #[requires="self.valid(vec.y_size(), vec.x_size())"]
    #[requires="forall y: usize, x: usize ::
                (0 <= x && x < vec.x_size() && 0 <= y && y < vec.y_size()) ==>
                vec.lookup(y, x) == 0 || vec.lookup(y, x) == 1"]
    fn mv(&mut self, vec: &mut Matrix) {
        assert!(vec.lookup(self.y, self.x) == 0 || vec.lookup(self.y, self.x) == 1);
        let pointer = vec.borrow(self.y, self.x);
        assert!(*pointer == 0 || *pointer == 1);
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
            North => self.y -= 1,   //~ ERROR: assertion might fail with "attempt to subtract with overflow"
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
 
fn main(){}
