trait Interface {
    type Statement;
    type Expression;
    type LabelSymbol;
}

mod parse;

vir_raw_block! { Ids =>
    index_vec::define_index_type! {
        pub struct BasicBlockId = usize;
    }

    index_vec::define_index_type! {
        pub struct StatementId = usize;
    }
}

pub struct BasicBlock {
    pub statements: index_vec::IndexVec<StatementId, Statement>,
    pub successors: Vec<BasicBlockId>,
}

pub struct GuardedBasicBlock {
    pub label: LabelSymbol,
    pub guard: Expression,
    pub statements: IndexVec<StatementId, Statement>,
    pub successors: Vec<BasicBlockId>,
}

vir_raw_block! { BasicBlockWithSuccessors =>
    impl crate::common::cfg::BasicBlockWithSuccessors for BasicBlock {
        type BasicBlockId = BasicBlockId;
        fn successors(&self) -> &[Self::BasicBlockId] {
            &self.successors
        }
    }
}
