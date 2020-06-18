fn M()
{
    let mut i = 0;
    let mut x = 0;
    let mut y = 0;
    let mut p: &mut u32 = &mut x;
    while true {
        i = i + 1;
        if(i == x) {
            p = &mut x; //~ ERROR reborrow
        } else {
            p = &mut y; //~ ERROR reborrow
        }
    }
}

fn main(){}
