
struct List<'a> {
    value: u32,
    next: Option<&'a mut List<'a>>,
}

fn test<'a, 'b>(l: &'b mut List<'a>) -> &'b mut List<'a> {
    let mut curr = l;
    loop {
        match curr.next {
            Some(ref mut next) => {
                curr = next;
            }
            None => {
                break;
            }
        }
    }
    curr
}

fn main() {}
