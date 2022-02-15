use prusti_contracts::*;

struct Example {
    m2: u32, // multiple of 2
    m3: u32, // multiple of 3
    m5: u32, // multiple of 5
    m7: u32, // multiple of 7
}

impl Example {
    #[pure]
    fn valid(&self) -> bool {
        self.m2 % 2 == 0 &&
        self.m3 % 3 == 0 &&
        self.m5 % 5 == 0 &&
        self.m7 % 7 == 0
    }

    #[requires(self.valid())]
    #[ensures(*result == old(self.m3))]
    #[assert_on_expiry(
        *result % 3 == 0,
        self.valid()
    )]
    fn m3_mut(&mut self) -> &mut u32 {
        &mut self.m3
    }

    #[requires(self.valid())]
    #[ensures(*result == old(self.m3))]
    #[assert_on_expiry(
        true,
        self.valid()     //~ ERROR pledge in the postcondition might not hold
    )]
    fn m3_mut_fail(&mut self) -> &mut u32 {
        &mut self.m3
    }
}

#[requires(arg.valid())]
#[ensures(arg.valid())]
fn test(arg: &mut Example) {
    let m3 = arg.m3_mut();
    *m3 += 3;
}

#[requires(arg.valid())]
#[ensures(arg.valid())]
fn test_fail(arg: &mut Example) {
    let m3 = arg.m3_mut(); //~ ERROR obligation might not hold on borrow expiry
    *m3 += 5; // mistake
}

fn main() {}
