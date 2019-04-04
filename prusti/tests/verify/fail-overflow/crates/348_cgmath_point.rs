/// From crate 348_cgmath

extern crate prusti_contracts;

use std::ops::Div;

#[derive(PartialEq, Eq, Copy, Clone, Hash)]
pub struct Point3<S> {
    pub x: S,
    pub y: S,
    pub z: S,
}

impl<S> Point3<S> {
    #[trusted]
    fn new(x: S, y: S, z: S) -> Point3<S> {
        Point3 {
            x,
            y,
            z
        }
    }
}

impl Div<Point3<isize>> for isize {
    type Output = Point3<isize>;

    fn div(self, other: Point3<isize>) -> Point3<isize> {
        let (scalar, point) = (self, other);
        Point3::new(
            (scalar / point.x), (scalar / point.y), (scalar / point.z), //~ ERROR overflow
        )
    }
}

fn main() {}
