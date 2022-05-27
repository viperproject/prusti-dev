use prusti_contracts::*;

trait Foo {
    type Type: Copy;

    #[trusted]
    #[pure]
    fn foo(&self) -> Self::Type {
        unimplemented!()
    }
}

fn main() {

}