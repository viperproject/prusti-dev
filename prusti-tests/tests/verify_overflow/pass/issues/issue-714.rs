use prusti_contracts::*;

#[derive(Clone, Copy)]
pub enum E {
    A,
    B,
    C
}

impl E {
    #[pure]
    pub fn len(&self) -> usize {
        0
    }
}

#[pure]
pub fn a() -> E {
    E::A
}

#[pure]
pub fn test() -> usize {
    a().len()
}

fn main() {}
