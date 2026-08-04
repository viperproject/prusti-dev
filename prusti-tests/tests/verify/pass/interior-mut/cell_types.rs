// `Cell` with different content types (Copy and non-Copy structs, `Option`,
// nested cells, slices of cells), generic functions over `Cell<T>`, and the
// `Cell` trait implementations (`Clone`, `Default`, `From`, comparisons).

use std::cell::Cell;

#[derive(Clone, Copy, PartialEq, Eq)]
struct Point {
    x: i32,
    y: i32,
}

fn copy_struct_content() {
    let c = Cell::new(Point { x: 1, y: 2 });
    let p = c.get();
    c.set(Point { x: p.y, y: p.x });
    assert!(c.get().x == 2);
    assert!(c.get().y == 1);
}

struct Pair {
    a: i32,
    b: i32,
}

fn non_copy_content() {
    let c = Cell::new(Pair { a: 1, b: 2 });
    let old = c.replace(Pair { a: 3, b: 4 });
    assert!(old.a == 1 && old.b == 2);
    let cur = c.into_inner();
    assert!(cur.a == 3 && cur.b == 4);
}

fn option_content() {
    let c = Cell::new(Some(3));
    let v = c.take();
    assert!(v == Some(3));
    assert!(c.get() == None);
    c.set(Some(4));
    assert!(c.get() == Some(4));
}

fn nested_cell() {
    let outer = Cell::new(Cell::new(1));
    let inner = outer.replace(Cell::new(2));
    assert!(inner.get() == 1);
    assert!(outer.into_inner().get() == 2);
}

fn generic_set_then_get<T: Copy + PartialEq>(c: &Cell<T>, v: T) {
    c.set(v);
    assert!(c.get() == v);
}

fn generic_callers() {
    let a = Cell::new(0u8);
    generic_set_then_get(&a, 5);
    let b = Cell::new(false);
    generic_set_then_get(&b, true);
    let p = Cell::new(Point { x: 0, y: 0 });
    generic_set_then_get(&p, Point { x: 1, y: 1 });
}

fn slice_of_cells() {
    let mut data = [1, 2, 3];
    let all: &Cell<[i32]> = Cell::from_mut(&mut data[..]);
    let cells: &[Cell<i32>] = all.as_slice_of_cells();
    cells[0].set(10);
    cells[2].set(30);
    assert!(cells[0].get() == 10);
    assert!(cells[1].get() == 2);
    assert!(cells[2].get() == 30);
    assert!(data[0] == 10 && data[1] == 2 && data[2] == 30);
}

fn clone_is_independent() {
    let a = Cell::new(1);
    let b = a.clone();
    a.set(5);
    assert!(a.get() == 5);
    assert!(b.get() == 1);
}

fn default_is_default() {
    let c: Cell<i32> = Cell::default();
    assert!(c.get() == 0);
}

fn from_value() {
    let c = Cell::from(8);
    assert!(c.get() == 8);
}

fn comparisons_use_contents() {
    let a = Cell::new(1);
    let b = Cell::new(1);
    assert!(a == b);
    b.set(2);
    assert!(a != b);
    assert!(a < b);
    assert!(b > a);
}

fn main() {
    copy_struct_content();
    non_copy_content();
    option_content();
    nested_cell();
    generic_callers();
    slice_of_cells();
    clone_is_independent();
    default_is_default();
    from_value();
    comparisons_use_contents();
}
