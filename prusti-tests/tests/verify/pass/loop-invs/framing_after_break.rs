use prusti_contracts::*;

#[trusted]
fn random() -> i32 {
    unimplemented!()
}

fn test() {
    let x = 123;

    'myloop: while {
        if random() < x {
            break 'myloop;
        }

        random() < 345
    } {
        if random() < 456 {
            break;
        }

        let y = Box::new(x);
    }

    assert!(x == 123);
}

fn test2() {
    let mut x: i32;

    'myloop: while {
        x = 123;

        if random() < x {
            break 'myloop;
        }

        random() < 345
    } {
        body_invariant!(x == 123);
        if random() < 456 {
            break;
        }

        let y = Box::new(x);
    }

    assert!(x == 123);
}

fn test3() {
    let mut x: i32;

    'myloop: while {
        x = 123;

        if random() < x {
            break 'myloop;
        }

        random() < 345
    } {
        body_invariant!(x == 123);
        if random() < 456 {
            break;
        }

        x = 567;

        let y = Box::new(x);
    }

    assert!(x == 123);
}

fn main() {}
