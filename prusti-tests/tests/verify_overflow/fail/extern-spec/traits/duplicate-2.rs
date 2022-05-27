use prusti_contracts::*;

#[extern_spec]
trait Iterator {
    #[requires(true)]
    fn next(&mut self) -> Option<Self::Item>;
}

#[extern_spec]
trait Iterator { 
    #[requires(true)]
    fn next(&mut self) -> Option<Self::Item>; //~ ERROR: duplicate specification for std::iter::Iterator::next
}

fn main() {}
