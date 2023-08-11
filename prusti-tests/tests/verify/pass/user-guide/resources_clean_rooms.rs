//// ANCHOR: nothing
//// ANCHOR_END: nothing
// The next line is only required for doctests, you can ignore/remove it
extern crate prusti_contracts;
use prusti_contracts::*;

fn main() {}

//// ANCHOR: code
resource! {
    fn cleaned(amount: usize, room_no: u32);
}

#[trusted]
#[ensures(cleaned(1, room_no))]
fn clean_room(room_no: u32) {
    // ... cleaning ...
}

#[ensures(forall(|room_no: u32| 1 <= room_no && room_no <= last_room_no ==> cleaned(1, room_no)))]
fn clean_all_rooms(last_room_no: u32) {
    let mut i = 1;
    while i <= last_room_no {
        body_invariant!(forall(|room_no: u32| 1 <= room_no && room_no < i ==> cleaned(1, room_no)));
        clean_room(i);
        i += 1;
    }
}
//// ANCHOR_END: code
