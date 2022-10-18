fn exit_loop_with_a_non_boolean_switch(
    a: usize,
    b: usize,
) {
    loop {
        match a.cmp(&b) {
            std::cmp::Ordering::Less => {},
            std::cmp::Ordering::Equal => return,
            std::cmp::Ordering::Greater => {}
        }
    }
}

fn main(){}
