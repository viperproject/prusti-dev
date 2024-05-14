use prusti_contracts::*;

struct Point<T> {
    x: T,
    y: T,
}

impl<T: Copy> Point<T> {
    #[pure]
    fn new(x: T, y: T) -> Point<T> {
        Point { x, y }
    }

    #[pure]
    fn x(self) -> T {
        self.x
    }

    #[pure]
    fn y(self) -> T {
        self.y
    }
}

#[ensures(Point::new(1, 2).x() == 1)]
fn main() {}
