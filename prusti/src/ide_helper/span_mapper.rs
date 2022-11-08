use prusti_common::config;
use prusti_interface::{
    environment::Environment,
    specs::typed,
};
use prusti_rustc_interface::{
    hir::{
        self,
        ItemId,
        Node,
        def_id::LocalDefId,
        BodyId,
        ItemKind,
    },
    middle::hir::map::Map,
    span::Span,
    middle::ty::TyCtxt,
};

use super::body_finder;


// use rustc_hir::hir::{ItemId};

fn collect_functions(hir: Map) {
    for i in hir.items() {
        let node = hir.get(i.hir_id());
        //let mut res = Vec::new();
        match node {
            Node::Item(item) => {
                println!("found an item");
            },
            _ => println!("found something else"),
        }
    }
}



// fn span_from_offset(offset: u32) -> Span {
//     
// }


pub fn map_span(env: &Environment<'_>, _def_spec: &typed::DefSpecificationMap) {
    // should only be called if we already checked that this argument was given
    let offset: u32 = 42; //config::spaninfo().unwrap();
    let tcx: TyCtxt = env.tcx();
    let hir: Map<'_> = tcx.hir();
    let path = env.name.source_path();
    let name = path.to_str().unwrap().clone();
    let pos: usize = offset.try_into().unwrap();
    // println!("env name: {}", env.name.source_path().display());
    // println!("char offset: {}", offset);

    // turn offset into span:
    let span: Span = body_finder::charoffset_to_span(offset, offset, tcx);
    println!("function identifier: {:#?}", span); 

    let mut bodies = body_finder::find_enclosing_bodies(env.tcx(), span);
    let body_id: hir::BodyId = bodies.next().unwrap();
    // let _def_id: LocalDefId = hir.body_owner_def_id(body_id);
    let body = hir.body(body_id);

    println!("the body : {:#?}", body);

    // let src_map: &SourceMap = env.tcx().sess.source_map();
}

    // let all_bodies = hir
    //     .items()
    //     .filter_map(|id| match hir.item(id).kind {
    //       ItemKind::Fn(_, _, body) => Some(body),
    //       _ => None,
    // });



    // let target: Node = hir.get(body.hir_id);

    // search target for the matching expression:
    // collect_functions(hir);  
    // for i in hir.items() {
    //     let item = hir.item(i);
    //     println!("found item: {:#?}", item);
    // }
    //
    // for i in hir.items() {
    //     let item : ItemId = i;
    //     let node : Node = hir.get(item.hir_id());
    //     let item_span: Span = node.ident().unwrap().span;
    //     // let body = item
    //     println!("found matching span for node: {:#?}", node);
    // }


    // I guess we can iterate over bodies to find the span of what 
    // we are looking for:


    // the information flow analysis crashes for some reason.
    //let body_with_facts = borrowck_facts::get_body_with_borrowck_facts(tcx, def_id);

    // println!("body_id: {:?}", body);
    //let results = flowistry::infoflow::compute_flow(tcx, body, body_with_facts);
    //let location_domain = results.analysis.location_domain();


