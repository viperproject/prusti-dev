// compile-flags: -Psif=true -Pserver_address=MOCK
// The sif flag is used in the server which, during the compiletest is only spawned with the default config.
// So we need to start a new server with this test config to make it work.

use prusti_contracts::*;

struct Wrapper<T>(T);

impl<T: Copy + PartialEq> Wrapper<T> {
    #[pure]
    fn get(&self) -> &T {
        &self.0
    }

    // #[after_expiry(low(before_expiry(*result)) ==> low(self.get()))]
    #[after_expiry(before_expiry(*result) == *self.get())]
    fn get_mut(&mut self) -> &mut T {
        &mut self.0
    }
}

#[trusted]
#[ensures(low(result))]
fn produce_low() -> u32 {
    todo!()
}

fn main() {
    let mut m = Wrapper(42);

    *m.get_mut() = produce_low();
    prusti_assert!(low(m.get()));
}
