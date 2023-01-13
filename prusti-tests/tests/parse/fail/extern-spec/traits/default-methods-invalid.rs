use prusti_contracts::*;

trait MyTrait {
    fn foo(&self) -> i32 {
        42
    }
}


#[extern_spec]
trait MyTrait {
    #[ensures(result == 42)]
    fn foo(&self) -> i32 { //~ ERROR: Unexpected method body. (Extern specs only define specifications.)
        43
    }
}

fn main() {
}
