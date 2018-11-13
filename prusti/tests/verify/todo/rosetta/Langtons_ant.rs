/// An adaptation of the example from
/// https://rosettacode.org/wiki/Langton%27s_ant#Rust

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
    #[ensures="result.valid()"]
    //TODO
    //#[ensures="forall y: usize, x: usize ::
    //            (0 <= x && x < self._ghost_x_size && 0 <= y && y < self._ghost_y_size) ==>
    //            self.lookup(y, x) == 0 || self.lookup(y, x) == 1"]
    fn new(y_size: usize, x_size: usize) -> Self {
        Self {
            _ghost_y_size: y_size,
            _ghost_x_size: x_size,
            vec: vec![vec![0; y_size]; x_size],
        }
    }

    #[trusted]
    fn borrow(&mut self, y: usize, x: usize) -> &mut u8 {
        &mut self.vec[y][x]
    }

    #[pure]
    #[trusted]
    fn lookup(&self, y: usize, x: usize) -> u8 {
        self.vec[y][x]
    }

    #[pure]
    //FIXME
    #[requires="forall y: usize, x: usize ::
                (0 <= x && x < self._ghost_x_size && 0 <= y && y < self._ghost_y_size) ==>
                self.lookup(y, x) == 0 || self.lookup(y, x) == 1"]
    fn valid(&self) -> bool {
        true
    }

}

#[trusted]
fn xor(a: u8, b: u8) -> u8 {
    a ^ b
}
 
impl Ant {
    #[requires="vec.valid()"]
    fn mv(&mut self, vec: &mut Matrix) {
        let pointer = vec.borrow(self.y, self.x);
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
 
    while ant.x < 100 && ant.y < 100 {
        ant.mv(&mut grid);
    }
    print_grid(&mut grid);
}
