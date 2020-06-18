// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use encoder::vir;
use encoder::Encoder;
use rustc::ty;


const SNAPSHOT_DOMAIN_SUFFIX:&str = "$Snap";
const SNAPSHOT_CONS_SUFFIX:&str = "$cons";

pub struct DomainEncoder<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> {
    encoder: &'p Encoder<'v, 'r, 'a, 'tcx>,
    ty: ty::Ty<'tcx>, // TODO this is the type we are talking about
}

impl<'p, 'v, 'r: 'v, 'a: 'r, 'tcx: 'a> DomainEncoder<'p, 'v, 'r, 'a, 'tcx> {
    pub fn new(encoder: &'p Encoder<'v, 'r, 'a, 'tcx>, ty: ty::Ty<'tcx>) -> Self {
        DomainEncoder { encoder, ty }
    }

    pub fn encode_snap_domain_def(self) -> vir::Domain {
        vir::Domain {
            name: self.encode_snap_domain_name(),
            functions: self.encode_snap_functions(),
            axioms: self.encode_snap_axioms(),
            type_vars: vec![]
        }
    }

    pub fn encode_snap_domain_name(&self) -> String {
        let mut name = self.encoder.encode_type_predicate_use(self.ty).clone();
        name.push_str(SNAPSHOT_DOMAIN_SUFFIX);
        name
    }

    fn encode_snap_functions(&self) -> Vec<vir::DomainFunction> {

        let domain_name = self.encode_snap_domain_name();

        let cons_fun = vir::DomainFunction {
            name: self.encode_snap_cons_name(),
            formal_args: vec![],
            return_type: vir::Type::Domain(domain_name.clone()),
            unique: false,
            domain_name,
        };
        vec![cons_fun]
    }

    fn encode_snap_cons_name(&self) -> String {
        let mut name = self.encoder.encode_type_predicate_use(self.ty).clone();
        name.push_str(SNAPSHOT_CONS_SUFFIX);
        name
    }

    fn encode_snap_axioms(&self) -> Vec<vir::DomainAxiom> {
        vec![] // TODO
    }

    pub fn encode_snap_cons_use(&self) -> String {
        unimplemented!()
    }

    pub fn encode_snap_compute_def(&self) -> vir::Function {
        unimplemented!()
    }

    pub fn encode_snap_compute_use(&self) -> String {
        unimplemented!()
    }
}
