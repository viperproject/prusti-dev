struct Link {next: Box<List>}
type List = Option<Link>;

#[analyzer::run]
fn test(mut l1: List, mut l2: List)
{
    let mut list1 = &mut l1;
    let mut list2 = &mut l2;
    // while let (Some(next_link_1), Some(next_link_2)) = (list1, list2) {
        
    while let Some(next_link_1) = list1 {
        if let Some(next_link_2) = list2 {
            list2 = &mut next_link_1.next;
            list1 = &mut next_link_2.next;
        } else {
            break;
        }
    }
}


fn main() { }
