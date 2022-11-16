fn foo(x: i32) -> i32 {
    unreachable!(); //~ ERROR unreachable!(..) statement might be reachable
}

fn main(){}
