use prusti_contracts::*;

#[derive(PartialEq, Eq)]
pub struct Point {
    x: i32,
    y: i32,
}

#[pure]
fn equal_points1(a: &Point, b: &Point) -> bool {
    *a == *b
}

predicate! {
    fn equal_points2(a: &Point, b: &Point) -> bool {
        *a == *b
    }
}


#[pure]
fn equal_points3(a: Point, b: Point) -> bool {  //~ ERROR: pure function parameters must be Copy
    a == b
}

impl Point {
    #[ensures(*self == result)]
    pub fn clone1(&self) -> Self {
        Self {
            ..*self
        }
    }
    #[ensures(*old(self) == result)]
    pub fn clone2(&self) -> Self {
        Self {
            ..*self
        }
    }
    #[ensures(equal_points1(old(self), &result))]
    pub fn clone3(&self) -> Self {
        Self {
            ..*self
        }
    }
    #[ensures(equal_points2(old(self), &result))]
    pub fn clone4(&self) -> Self {
        Self {
            ..*self
        }
    }
    #[ensures(old(self) == result)]
    pub fn move1(self) -> Self {
        self
    }
    #[ensures(equal_points3(old(self), result))]    //~ ERROR: pure function parameters must be Copy
    pub fn move2(self) -> Self {
        self
    }
}

fn main() {}
