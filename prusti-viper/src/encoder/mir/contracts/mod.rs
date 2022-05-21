//! Procedure contracts enriched with borrow information.

mod borrows;
#[allow(clippy::module_inception)]
mod contracts;
mod interface;

pub(crate) use contracts::{ProcedureContract, ProcedureContractMirDef};
pub(crate) use interface::{ContractsEncoderInterface, ContractsEncoderState};
