#![feature(rustc_private)]
#![feature(associated_type_defaults)]
#![feature(box_patterns)]

extern crate rustc_middle;
extern crate rustc_serialize;
extern crate rustc_type_ir;

mod encoders;

use prusti_interface::{environment::EnvBody, specs::typed::SpecificationItem};
use prusti_rustc_interface::{
    middle::ty,
    hir,
};

pub fn test_entrypoint<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    body: EnvBody<'tcx>,
    def_spec: prusti_interface::specs::typed::DefSpecificationMap,
) -> vir::Program<'tcx> {
    use task_encoder::TaskEncoder;

    crate::encoders::init_def_spec(def_spec);
    vir::init_vcx(vir::VirCtxt::new(tcx, body));

    // TODO: this should be a "crate" encoder, which will deps.require all the methods in the crate

    for def_id in tcx.hir().body_owners() {
        tracing::debug!("test_entrypoint item: {def_id:?}");
        let kind = tcx.def_kind(def_id);
        match kind {
            hir::def::DefKind::Fn |
            hir::def::DefKind::AssocFn => {
                let def_id = def_id.to_def_id();
                if prusti_interface::specs::is_spec_fn(tcx, def_id) {
                    continue;
                }

                let (is_pure, is_trusted) = crate::encoders::with_proc_spec(def_id, |proc_spec| {
                        let is_pure = proc_spec.kind.is_pure().unwrap_or_default();
                        let is_trusted = proc_spec.trusted.extract_inherit().unwrap_or_default();
                        (is_pure, is_trusted)
                }).unwrap_or_default();

                if !(is_trusted && is_pure) {
                    let substs = ty::GenericArgs::identity_for_item(tcx, def_id);
                    let res = crate::encoders::MirImpureEnc::encode((def_id, substs, None));
                    assert!(res.is_ok());
                }
            }
            unsupported_item_kind => {
                tracing::debug!("unsupported item: {unsupported_item_kind:?}");
            }
        }
    }

    fn header(code: &mut String, title: &str) {
        code.push_str("// -----------------------------\n");
        code.push_str(&format!("// {}\n", title));
        code.push_str("// -----------------------------\n");
    }
    let mut viper_code = String::new();

    header(&mut viper_code, "methods");
    for output in crate::encoders::MirImpureEnc::all_outputs() {
        viper_code.push_str(&format!("{:?}\n", output.method));
    }

    header(&mut viper_code, "functions");
    for output in crate::encoders::MirFunctionEnc::all_outputs() {
        viper_code.push_str(&format!("{:?}\n", output.function));
    }

    header(&mut viper_code, "MIR builtins");
    for output in crate::encoders::MirBuiltinEnc::all_outputs() {
        viper_code.push_str(&format!("{:?}\n", output.function));
    }

    header(&mut viper_code, "generics");
    for output in crate::encoders::GenericEnc::all_outputs() {
        viper_code.push_str(&format!("{:?}\n", output.snapshot_param));
        viper_code.push_str(&format!("{:?}\n", output.predicate_param));
        viper_code.push_str(&format!("{:?}\n", output.domain_type));
    }

    header(&mut viper_code, "snapshots");
    for output in crate::encoders::DomainEnc_all_outputs() {
        viper_code.push_str(&format!("{:?}\n", output));
    }

    header(&mut viper_code, "types");
    for output in crate::encoders::PredicateEnc::all_outputs() {
        for field in output.fields {
            viper_code.push_str(&format!("{:?}", field));
        }
        for field_projection in output.ref_to_field_refs {
            viper_code.push_str(&format!("{:?}", field_projection));
        }
        viper_code.push_str(&format!("{:?}\n", output.unreachable_to_snap));
        viper_code.push_str(&format!("{:?}\n", output.function_snap));
        for pred in output.predicates {
            viper_code.push_str(&format!("{:?}\n", pred));
        }
        viper_code.push_str(&format!("{:?}\n", output.method_assign));
    }

    std::fs::write("local-testing/simple.vpr", viper_code).unwrap();

    vir::with_vcx(|vcx|
        vcx.mk_program(
            &[],
            &[],
            &[],
            vcx.alloc_slice(&[
                vcx.mk_function("test_function", &[], &vir::TypeData::Bool, &[], &[], None),
            ]),
            &[]
        )
    )
}
