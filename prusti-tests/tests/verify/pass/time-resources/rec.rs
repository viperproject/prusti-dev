// compile-flags: -Ptime_reasoning=true

use prusti_contracts::*;

#[extern_spec]
impl usize {
    #[pure]
    #[ensures(self.pow(n) * self == self.pow(n + 1))]
    #[ensures(self >= 1 ==> result >= 1)]
    #[ensures(self >= 1 ==> self.pow(0) == 1)]
    fn pow(self, n: u32) -> usize;
}

#[requires(time_credits(2_usize.pow(n as u32)))]
fn fib(n: usize) -> usize {
    if n <= 1 {
        1
    } else {
        fib(n - 1) + fib(n - 2)
    }
}

#[requires(time_credits(50))]
fn main() {
    // consumes 32 credits
    fib(5);
}
