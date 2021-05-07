use std::collections::HashMap;

use rustc_middle::{mir, ty, ty::TyCtxt};
use rustc_hir::{def_id::DefId};
use rustc_mir::borrow_check::facts::AllFacts;
use rustc_mir::borrow_check::location::LocationTable;

mod extract;
mod derive;

pub(super) use self::extract::enrich_mir_body;

/// A wrapper around MIR body that hides unnecessary details.
pub struct MirBody<'tcx> {
    def_id: DefId,
    // Information obtained from the borrow checker.
    inputs_and_output: Vec<ty::Ty<'tcx>>,
    body: mir::Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    universal_regions: Vec<ty::RegionVid>,
    universal_regions_outlives: Vec<(ty::RegionVid, ty::RegionVid)>,
    polonius_facts: AllFacts,
    location_table: LocationTable,
    // Derived information.
    /// The names of local variables.
    local_names: HashMap<mir::Local, String>,
}

pub struct Variable<'body, 'tcx> {
    id: mir::Local,
    decl: &'body mir::LocalDecl<'tcx>,
    body: &'body MirBody<'tcx>,
}

pub struct BasicBlock<'body, 'tcx> {
    index: mir::BasicBlock,
    data: &'body mir::BasicBlockData<'tcx>,
    body: &'body MirBody<'tcx>,
}

pub struct Statement<'body, 'tcx> {
    location: mir::Location,
    statement: &'body mir::Statement<'tcx>,
    body: &'body MirBody<'tcx>,
}

pub struct Terminator<'body, 'tcx> {
    location: mir::Location,
    terminator: &'body mir::Terminator<'tcx>,
    body: &'body MirBody<'tcx>,
}

impl<'tcx> MirBody<'tcx> {
    pub fn iter_locals<'a>(&'a self) -> impl Iterator<Item=Variable<'a, 'tcx>> {
        self.body.local_decls.iter_enumerated().map(move |(id, decl)| {
            Variable {
                id,
                decl,
                body: self,
            }
        })
    }
    pub fn basic_block_indices(&self) -> impl Iterator<Item=mir::BasicBlock> {
        self.body.basic_blocks().indices()
    }
    pub fn get_block<'a>(&'a self, index: mir::BasicBlock) -> BasicBlock<'a, 'tcx> {
        BasicBlock {
            index,
            data: &self.body[index],
            body: self,
        }
    }
}

impl<'body, 'tcx> Variable<'body, 'tcx> {
    /// Return the user-friendly name of the variable.
    pub fn name(&self) -> Option<&str> {
        self.body.local_names.get(&self.id).map(|s| s.as_ref())
    }
    /// Return the identifier of the variable.
    pub fn id(&self) -> mir::Local {
        self.id
    }
    /// Return the type of the variable.
    pub fn ty(&self) -> ty::Ty<'tcx> {
        self.decl.ty
    }
}

impl<'body, 'tcx> BasicBlock<'body, 'tcx> {
    pub fn iter_statements<'a>(&'a self) -> impl Iterator<Item=Statement<'a, 'tcx>> {
        self.data.statements.iter().enumerate().map(
            move |(index, statement)| {
                Statement {
                    location: mir::Location {
                        block: self.index,
                        statement_index: index,
                    },
                    statement,
                    body: self.body
                }
            }
        )
    }
    pub fn terminator<'a>(&'a self) -> Option<Terminator<'a, 'tcx>> {
        self.data.terminator.as_ref().map(|terminator| {
            Terminator {
                location: mir::Location {
                    block: self.index,
                    statement_index: self.data.statements.len(),
                },
                terminator,
                body: self.body,
            }
        })
    }
}

impl<'body, 'tcx> Statement<'body, 'tcx> {
    pub fn index(&self) -> usize {
        self.location.statement_index
    }
    pub fn kind(&self) -> &mir::StatementKind<'tcx> {
        &self.statement.kind
    }
}

impl<'body, 'tcx> Terminator<'body, 'tcx> {
    pub fn basic_block(&self) -> mir::BasicBlock {
        self.location.block
    }
    pub fn kind(&self) -> &mir::TerminatorKind<'tcx> {
        &self.terminator.kind
    }
}