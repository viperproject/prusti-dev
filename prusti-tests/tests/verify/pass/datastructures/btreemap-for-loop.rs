use std::collections::BTreeMap;

pub fn btreemap_basic() {
    let mut m: BTreeMap<i32, &'static str> = BTreeMap::new();
    m.insert(2, "two");
    m.insert(1, "one");
    m.insert(3, "three");
    let mut total = 0;
    for (k, _v) in &m {
        total += k;
    }
    let _ = total;
}

fn main() {}
