// compile-flags: -Penable_ghost_constraints=true

use prusti_contracts::*;

trait HasContract {
    #[pure]
    fn pre(&self) -> bool;
    #[pure]
    fn post(&self) -> bool;
}

trait MyTrait {
    fn foo(&mut self);
}

#[extern_spec] //~ ERROR: the method's precondition may not be a valid weakening of the trait's precondition
trait MyTrait {
    #[ghost_constraint(Self: HasContract, [
        requires(self.pre()), ensures(self.post())
    ])]
    fn foo(&mut self);
}

struct MyStruct {
    x: i32,
}

#[refine_trait_spec]
impl MyTrait for MyStruct {
    #[requires(self.x >= 15)]
    fn foo(&mut self) {
        self.x += 10;
    }
}

impl HasContract for MyStruct {
    #[pure]
    fn post(&self) -> bool {
        self.x >= 20
    }

    #[pure]
    fn pre(&self) -> bool {
        self.x >= 10
    }
}

fn main() {
}