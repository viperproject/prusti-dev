
//#![feature(nll)]

struct List {
    next: Option<Box<List>>,
}

fn use_list(_l: &mut List) {}

fn test(l: &mut List) -> &mut List {
    let mut c = l;
    let mut end = false;
    while !end {
        match c.next {
            Some(ref mut next) => {
                c = next;
            },
            None => {
                end = true;
            }
        }
    }
    use_list(c);
    c
}

/*
fn test2(mut l: List) {
    let mut c = &mut l;
    let mut end = false;
    while !end {
        match c.next {
            Some(ref mut next) => {
                c = next;
            },
            None => {
                end = true;
            }
        }
    }
    use_list(c);
}

fn test3(l: &mut List) -> &mut List {
    if let Some(ref mut c) = l.next {
        let mut c = c;
        let mut end = false;
        while !end {
            match c.next {
                Some(ref mut next) => {
                    c = next;
                },
                None => {
                    end = true;
                }
            }
        }
        use_list(c);
        c
    } else {
        l
    }
}
*/

fn main() {
    //test(List {next: None});
    test(&mut List {next: None});
}
