use prusti_contracts::*;

trait Model {
  type Kind;
}

struct MyModel {}

impl Model for MyModel {
  type Kind = bool;
}

struct Guard<M: Model> {
  kind: M::Kind,
}

// <MyModel as Model>::Kind is the same type as bool,
// but it need to be normalized to see that.
fn test1(gd: Guard<MyModel>) -> bool {
  gd.kind
}

// Snapshot types should also be normalized.
#[pure]
fn test2(gd: &Guard<MyModel>) -> bool {
  gd.kind
}

// In this case, normalization fails, so it should
// continue with the non-normalized type.
fn test3<M: Model>(gd: Guard<M>) {}

#[trusted]
fn main() {}
