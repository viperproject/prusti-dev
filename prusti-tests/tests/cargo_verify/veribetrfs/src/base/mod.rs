pub mod option;
pub mod vector;

pub use option::Opt;
pub use vector::Vector;

pub fn replace<T>(dest: &mut T, src: T) -> T {
    std::mem::replace(dest, src)
}
