/// Source: crate 342_euclid > transform3d > inverse
extern crate prusti_contracts;

use std::ops::{Add, Mul, Sub, Div, Neg};
use std::marker::PhantomData;

struct TypedTransform3D<T, Src, Dst> {
    pub m11: T, pub m12: T, pub m13: T, pub m14: T,
    pub m21: T, pub m22: T, pub m23: T, pub m24: T,
    pub m31: T, pub m32: T, pub m33: T, pub m34: T,
    pub m41: T, pub m42: T, pub m43: T, pub m44: T,
    _unit: PhantomData<(Src, Dst)>,
}

#[derive(Clone, Copy)]
struct UnknownUnit;

/// The default 3d transform type with no units.
type Transform3D<T> = TypedTransform3D<T, UnknownUnit, UnknownUnit>;

trait Zero {
    fn zero() -> Self;
}

trait One {
    fn one() -> Self;
}

trait Trig {
    fn sin(self) -> Self;
    fn cos(self) -> Self;
    fn tan(self) -> Self;
    fn fast_atan2(y: Self, x: Self) -> Self;
    fn degrees_to_radians(deg: Self) -> Self;
    fn radians_to_degrees(rad: Self) -> Self;
}

impl<T, Src, Dst> TypedTransform3D<T, Src, Dst> {
    fn row_major(
        m11: T, m12: T, m13: T, m14: T,
        m21: T, m22: T, m23: T, m24: T,
        m31: T, m32: T, m33: T, m34: T,
        m41: T, m42: T, m43: T, m44: T)
        -> Self {
        TypedTransform3D {
            m11,
            m12,
            m13,
            m14,
            m21,
            m22,
            m23,
            m24,
            m31,
            m32,
            m33,
            m34,
            m41,
            m42,
            m43,
            m44,
            _unit: PhantomData,
        }
    }
}

impl <T, Src, Dst> TypedTransform3D<T, Src, Dst>
where T: Copy + Clone +
         Add<T, Output=T> +
         Sub<T, Output=T> +
         Mul<T, Output=T> +
         Div<T, Output=T> +
         Neg<Output=T> +
         PartialOrd +
         Trig +
         One + Zero {

    /// Returns the inverse transform if possible.
    fn inverse(&self) -> Option<TypedTransform3D<T, Dst, Src>> {
        let det = self.determinant();

        if det == Zero::zero() {
            return None;
        }

        // todo(gw): this could be made faster by special casing
        // for simpler transform types.
        let m = TypedTransform3D::row_major(
            self.m23 * self.m34 * self.m42 - self.m24 * self.m33 * self.m42 +
            self.m24 * self.m32 * self.m43 - self.m22 * self.m34 * self.m43 -
            self.m23 * self.m32 * self.m44 + self.m22 * self.m33 * self.m44,
            self.m14 * self.m33 * self.m42 - self.m13 * self.m34 * self.m42 -
            self.m14 * self.m32 * self.m43 + self.m12 * self.m34 * self.m43 +
            self.m13 * self.m32 * self.m44 - self.m12 * self.m33 * self.m44,
            self.m13 * self.m24 * self.m42 - self.m14 * self.m23 * self.m42 +
            self.m14 * self.m22 * self.m43 - self.m12 * self.m24 * self.m43 -
            self.m13 * self.m22 * self.m44 + self.m12 * self.m23 * self.m44,
            self.m14 * self.m23 * self.m32 - self.m13 * self.m24 * self.m32 -
            self.m14 * self.m22 * self.m33 + self.m12 * self.m24 * self.m33 +
            self.m13 * self.m22 * self.m34 - self.m12 * self.m23 * self.m34,
            self.m24 * self.m33 * self.m41 - self.m23 * self.m34 * self.m41 -
            self.m24 * self.m31 * self.m43 + self.m21 * self.m34 * self.m43 +
            self.m23 * self.m31 * self.m44 - self.m21 * self.m33 * self.m44,
            self.m13 * self.m34 * self.m41 - self.m14 * self.m33 * self.m41 +
            self.m14 * self.m31 * self.m43 - self.m11 * self.m34 * self.m43 -
            self.m13 * self.m31 * self.m44 + self.m11 * self.m33 * self.m44,
            self.m14 * self.m23 * self.m41 - self.m13 * self.m24 * self.m41 -
            self.m14 * self.m21 * self.m43 + self.m11 * self.m24 * self.m43 +
            self.m13 * self.m21 * self.m44 - self.m11 * self.m23 * self.m44,
            self.m13 * self.m24 * self.m31 - self.m14 * self.m23 * self.m31 +
            self.m14 * self.m21 * self.m33 - self.m11 * self.m24 * self.m33 -
            self.m13 * self.m21 * self.m34 + self.m11 * self.m23 * self.m34,
            self.m22 * self.m34 * self.m41 - self.m24 * self.m32 * self.m41 +
            self.m24 * self.m31 * self.m42 - self.m21 * self.m34 * self.m42 -
            self.m22 * self.m31 * self.m44 + self.m21 * self.m32 * self.m44,
            self.m14 * self.m32 * self.m41 - self.m12 * self.m34 * self.m41 -
            self.m14 * self.m31 * self.m42 + self.m11 * self.m34 * self.m42 +
            self.m12 * self.m31 * self.m44 - self.m11 * self.m32 * self.m44,
            self.m12 * self.m24 * self.m41 - self.m14 * self.m22 * self.m41 +
            self.m14 * self.m21 * self.m42 - self.m11 * self.m24 * self.m42 -
            self.m12 * self.m21 * self.m44 + self.m11 * self.m22 * self.m44,
            self.m14 * self.m22 * self.m31 - self.m12 * self.m24 * self.m31 -
            self.m14 * self.m21 * self.m32 + self.m11 * self.m24 * self.m32 +
            self.m12 * self.m21 * self.m34 - self.m11 * self.m22 * self.m34,
            self.m23 * self.m32 * self.m41 - self.m22 * self.m33 * self.m41 -
            self.m23 * self.m31 * self.m42 + self.m21 * self.m33 * self.m42 +
            self.m22 * self.m31 * self.m43 - self.m21 * self.m32 * self.m43,
            self.m12 * self.m33 * self.m41 - self.m13 * self.m32 * self.m41 +
            self.m13 * self.m31 * self.m42 - self.m11 * self.m33 * self.m42 -
            self.m12 * self.m31 * self.m43 + self.m11 * self.m32 * self.m43,
            self.m13 * self.m22 * self.m41 - self.m12 * self.m23 * self.m41 -
            self.m13 * self.m21 * self.m42 + self.m11 * self.m23 * self.m42 +
            self.m12 * self.m21 * self.m43 - self.m11 * self.m22 * self.m43,
            self.m12 * self.m23 * self.m31 - self.m13 * self.m22 * self.m31 +
            self.m13 * self.m21 * self.m32 - self.m11 * self.m23 * self.m32 -
            self.m12 * self.m21 * self.m33 + self.m11 * self.m22 * self.m33
        );

        let _1: T = One::one();
        Some(m.mul_s(_1 / det))
    }

    /// Compute the determinant of the transform.
    fn determinant(&self) -> T {
        self.m14 * self.m23 * self.m32 * self.m41 -
        self.m13 * self.m24 * self.m32 * self.m41 -
        self.m14 * self.m22 * self.m33 * self.m41 +
        self.m12 * self.m24 * self.m33 * self.m41 +
        self.m13 * self.m22 * self.m34 * self.m41 -
        self.m12 * self.m23 * self.m34 * self.m41 -
        self.m14 * self.m23 * self.m31 * self.m42 +
        self.m13 * self.m24 * self.m31 * self.m42 +
        self.m14 * self.m21 * self.m33 * self.m42 -
        self.m11 * self.m24 * self.m33 * self.m42 -
        self.m13 * self.m21 * self.m34 * self.m42 +
        self.m11 * self.m23 * self.m34 * self.m42 +
        self.m14 * self.m22 * self.m31 * self.m43 -
        self.m12 * self.m24 * self.m31 * self.m43 -
        self.m14 * self.m21 * self.m32 * self.m43 +
        self.m11 * self.m24 * self.m32 * self.m43 +
        self.m12 * self.m21 * self.m34 * self.m43 -
        self.m11 * self.m22 * self.m34 * self.m43 -
        self.m13 * self.m22 * self.m31 * self.m44 +
        self.m12 * self.m23 * self.m31 * self.m44 +
        self.m13 * self.m21 * self.m32 * self.m44 -
        self.m11 * self.m23 * self.m32 * self.m44 -
        self.m12 * self.m21 * self.m33 * self.m44 +
        self.m11 * self.m22 * self.m33 * self.m44
    }

    fn mul_s(&self, x: T) -> Self {
        TypedTransform3D::row_major(
            self.m11 * x, self.m12 * x, self.m13 * x, self.m14 * x,
            self.m21 * x, self.m22 * x, self.m23 * x, self.m24 * x,
            self.m31 * x, self.m32 * x, self.m33 * x, self.m34 * x,
            self.m41 * x, self.m42 * x, self.m43 * x, self.m44 * x
        )
    }

}

fn main(){}
