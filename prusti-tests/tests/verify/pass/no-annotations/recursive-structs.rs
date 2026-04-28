struct A<K> {
    k: K,
    link: Option<Box<B<K>>>,
}
struct B<K> {
    data: A<K>,
}
fn main() {
    let _: A<i32> = A { k: 0, link: None };
}
