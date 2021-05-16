trait Interface {
    type Sort;
    type UninterpretedSortSymbol;
    type UninterpretedSortValue;
    type IdentSymbol;
}

pub enum Value {
    Bool(bool),
    Int(i64),
    Real,
    /// A value of a user-defined uninterpreted sort.
    Uninterpreted {
        sort: UninterpretedSortSymbol,
        value: UninterpretedSortValue,
    },
}

pub struct ModelItemArg {
    pub name: IdentSymbol,
    pub sort: Sort,
}

pub struct ModelItem {
    pub name: IdentSymbol,
    pub args: Vec<ModelItemArg>,
    pub sort: Sort,
    pub value: Value,
}

pub struct Model {
    pub items: Vec<ModelItem>,
}

impl Model {
    pub fn get_label(&self, label: &IdentSymbol) -> bool {
        for item in &self.items {
            if &item.name == label {
                if let Value::Bool(value) = item.value {
                    return value;
                } else {
                    unreachable!("{:?} is not a label", item);
                }
            }
        }
        unreachable!("did not find label {} in model", label);
    }
}
