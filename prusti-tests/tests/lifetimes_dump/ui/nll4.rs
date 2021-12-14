use std::collections::HashSet;

#[derive(PartialEq, Eq, Hash, Debug)]
struct T {
    x: u32,
}

struct List {
    value: T,
    next: Option<Box<List>>,
}

fn to_refs<'a>(mut list: &'a mut List) -> HashSet<&'a mut T>
    // ensures HashSet<RefT>(result) --* List(list) && HashSet$Drop<RefT>(result)
{
    let mut result = HashSet::new();
    let mut list = &mut *list;
    loop
    // invariant HashSet<RefT>(result) --* List(list) && HashSet$Drop<RefT>(result)
    {
        result.insert(&mut list.value);
        // let maybe_old_ref = result.insert(&mut list.value);
        // drop(maybe_old_ref);  // TODO: this should go into the footprint, but how?
        if let Some(n) = list.next.as_mut() {
            list = n;
        } else {
            return result;
        }
    }
}

fn main() {}
