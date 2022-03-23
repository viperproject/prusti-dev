pub mod linear_mutable_map;
pub mod linear_mutable_map_base;

enum A {
    One(u8),
    Two{fst: u8, snd: u8},
}

fn aaaa(a: &A) {
    match a {
        A::One(_) => (),
        A::Two{fst, snd}  if fst == snd => (),
        _ => ()
    }
}