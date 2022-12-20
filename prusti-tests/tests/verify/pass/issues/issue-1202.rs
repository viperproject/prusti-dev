fn main() {
    issue1202::test0_();
    issue1202::test1_();
    issue1202::test2_();
    issue1202::_test0();
    issue1202::_test1();
    issue1202::_test2();
    issue1202::test4_();
    issue1202::_test4();
}

#[deny(non_snake_case)]
mod issue1202 {
    use prusti_contracts::*;

    #[ensures(true)]
    pub fn test0_(){}

    #[requires(true)]
    pub fn test1_(){}

    #[requires(true)]
    #[ensures(true)]
    pub fn test2_(){}

    #[ensures(true)]
    pub fn _test0(){}

    #[requires(true)]
    pub fn _test1(){}

    #[requires(true)]
    #[ensures(true)]
    pub fn _test2(){}

    pub fn test4_(){} // no warnings
    pub fn _test4(){} // no warnings
}