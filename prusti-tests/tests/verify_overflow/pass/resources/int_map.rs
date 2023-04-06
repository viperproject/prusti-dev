use prusti_contracts::*;
use std::collections::HashMap;

#[invariant_twostate(
    forall(
        |key: u32|
            old(holds(Insert(self.id(), key))) == PermAmount::from(0) ==>
            self.get(key) === old(self.get(key)))
)]
struct IntMap<T: Copy>(HashMap<u32, T>);

#[derive(Clone, Copy)]
struct IntMapId(u32);

#[resource]
struct Insert(IntMapId, u32);

impl <T: Copy> IntMap<T> {

    #[pure]
    #[trusted]
    fn id(&self) -> IntMapId {
        unimplemented!()
    }

    #[requires(transfers(Insert(self.id(), key), 1))]
    #[ensures(transfers(Insert(self.id(), key), 1))]
    #[ensures(self.id() === old(self.id()))]
    #[ensures(self.get(key) === value)]
    #[trusted]
    fn insert(&mut self, key: u32, value: T) {
    }

    #[pure]
    #[trusted]
    fn get(&self, key: u32) -> T {
        todo!();
    }

    #[ensures(forall(|key: u32| transfers(Insert(result.id(), key), 1)))]
    fn new() -> IntMap<T> {
        let result = IntMap(HashMap::new());
        produces!(forall(|key: u32| transfers(Insert(result.id(), key), 1)));
        result
    }
}

fn main(){
    let mut map = IntMap::new();
    map.insert(1,2);
    map.insert(3,4);
    prusti_assert!(map.get(1) == 2);
}
