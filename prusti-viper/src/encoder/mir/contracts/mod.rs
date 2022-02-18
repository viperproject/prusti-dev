//! Procedure contracts enriched with borrow information.

mod borrows;
mod interface;

pub(crate) use interface::{
    ContractsEncoderInterface, ContractsEncoderState, ProcedureContract, ProcedureContractMirDef,
};
