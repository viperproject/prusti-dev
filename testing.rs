
enum Enum<T, V> {
    A(T),
    B(V),
}
struct Struct<T, V> {
    a: T,
    b: V,
}

fn baz<'a, 'b, T, V>(mut a: Struct<&'a mut T, &'b mut V>) {
    let (b, c) = (&*a.a, &*a.b);
    let d = &a;
    a = b;
    let y = match a {
        Enum::A(t) => None,
        Enum::B(v) => Some(&mut *v)
    };

    let x = x;
}

fn main() {}