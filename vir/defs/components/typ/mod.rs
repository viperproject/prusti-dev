trait Interface {
    type UninterpretedSortSymbol;
    type AdtNameSymbol;
}

mod display;

pub enum Type {
    Int,
    Bool,
    Real,
    Domain(DomainType),
}

pub struct DomainType {
    pub name: UninterpretedSortSymbol,
}

pub struct ReferenceType {
    pub name: AdtNameSymbol,
}
