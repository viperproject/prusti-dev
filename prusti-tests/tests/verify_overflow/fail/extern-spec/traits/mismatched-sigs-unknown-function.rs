use prusti_contracts::*;

#[extern_spec]
trait Iterator {
    fn foo(&mut self); //~ ERROR: cannot find method or associated constant `foo` in trait `Iterator`
}

fn main() {}
