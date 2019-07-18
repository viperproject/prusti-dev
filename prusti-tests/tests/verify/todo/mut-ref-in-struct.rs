extern crate prusti_contracts;

pub struct Token(pub usize);

pub struct Ready(usize);

pub struct UnixReady(Ready);

pub struct Event {
    kind: Ready,
    token: Token
}

pub struct MyStruct<'a> {
    event: &'a mut Event,
    unix_ready: &'a mut UnixReady,
}

pub fn kind_mut(event: &mut Event) -> &mut Ready {
    &mut event.kind
}

impl UnixReady {
    #[ensures="after_expiry( 0 + (self.0).0 == before_expiry(result.0) )"]
    fn deref_mut(&mut self) -> &mut Ready {
        &mut self.0
    }
}

pub fn test<'a>(my_struct: &'a mut MyStruct<'a>) {
    let mut ready = my_struct.unix_ready.deref_mut();
    ready.0 = 123;
    //(my_struct.unix_ready.0).0 += 1;
    assert!((my_struct.unix_ready.0).0 == 123);
}

//#[ensures="(result.unix_ready.0).0 == 123"]
pub fn test2<'a>(unix_ready: &'a mut UnixReady, event: &'a mut Event) {
    let mut my_struct = MyStruct { event, unix_ready };
    let ref_my_struct = &mut my_struct;
    test(ref_my_struct);
    assert!((my_struct.unix_ready.0).0 == 123);
    //my_struct
}

fn main() {}
