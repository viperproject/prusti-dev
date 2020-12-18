// compile-flags: -Pprint_desugared_specs=true -Pprint_typeckd_specs=true -Pskip_verify=true -Phide_uuids=true
// normalize-stdout-test: "[a-z0-9]{32}" -> "$(NUM_UUID)"
// normalize-stdout-test: "[a-z0-9]{8}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{12}" -> "$(UUID)"

use prusti_contracts::*;

trait Test1 {

    #[requires(true)]
    fn test1() {}

    #[ensures(true)]
    fn test2() {}

    #[requires(true)]
    fn test3();

    #[ensures(true)]
    fn test4();

}

trait Test2 {

    #[requires(true)]
    #[ensures(true)]
    fn test1() {}

    #[requires(true)]
    #[ensures(true)]
    fn test2();

}

trait Test3 {

    #[requires(true)]
    fn test1(&self) {}

    #[ensures(true)]
    fn test2(&self) {}

    #[requires(true)]
    fn test3(&self);

    #[ensures(true)]
    fn test4(&self);

}

trait Test4 {

    #[requires(true)]
    #[ensures(true)]
    fn test1(&self) {}

    #[requires(true)]
    #[ensures(true)]
    fn test2(&self);

}

fn main() {}
