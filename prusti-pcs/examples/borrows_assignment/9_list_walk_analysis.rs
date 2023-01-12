struct Link {next: Box<List>}
type List = Option<Link>;

#[analyzer::run]
fn test(mut l: List)
{
    let mut list = &mut l;
    while let Some(next_link) = list {
        list = &mut next_link.next;
    }
    let list_live = &mut (*list);
}


fn main() { }
