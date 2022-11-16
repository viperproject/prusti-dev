/// From crate 348_cgmath

use prusti_contracts::*;

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
            scalar / point.x, scalar / point.y, scalar / point.z, //~ ERROR
        )
    }
}

pub struct Vector1<S> {
    /// The x component of the vector.
    pub x: S,
}

impl<S> Vector1<S> {
    #[trusted]
    fn new(x: S) -> Vector1<S> {
        Vector1 {
            x,
        }
    }
}

impl Div<Vector1<u64>> for u64 {
    type Output = Vector1<u64>;

    fn div(self, other: Vector1<u64>) -> Vector1<u64> {
        let (scalar, point) = (self, other);
        Vector1::new(
            scalar / point.x, //~ ERROR
        )
    }
}

fn main() {}
