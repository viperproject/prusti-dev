use prusti_common::config;
use prusti_interface::environment::Environment;
use std::collections::HashMap;

use prusti_rustc_interface::{
    hir::{
        def::DefKind,
        def_id::DefId,
    },
    middle::ty::{
        TraitRef,
        DefIdTree,
        PredicateKind,
        TyCtxt,
        ImplSubject,
        Generics,
    },
};
use super::ide_info::ProcDef;


pub fn collect_queried_signatures(env: &Environment<'_>, fncalls: &Vec<ProcDef>) -> Option<String> {
    let def_path_str: String = config::query_method_signature()?;
    println!("\n\n\n\nCollecting Information for Queried Method");
    println!("Got query for external specification template for : {}", def_path_str);
    let existing = fncalls.iter().find(|procdef| procdef.name == def_path_str)?;

    // helpers: 
    let tcx = env.tcx();
    let defid: DefId = existing.defid;

    // check what kind of definition we are looking at:

    let def_kind = tcx.opt_def_kind(defid)?;
    match def_kind {
        DefKind::AssocFn => {
            let opt_item_name = tcx.opt_item_name(defid)?;
            let item_name = opt_item_name.as_str();
            println!("Item Name: {}", item_name);
            let impl_of_method_opt = tcx.impl_of_method(defid);
            match impl_of_method_opt {
                Some(impl_of_method) => {
                    println!("Impl of method : {:?}", impl_of_method);
                    let mut trait_name = None;
                    let impl_subj = tcx.impl_subject(impl_of_method);
                    let self_ty = match impl_subj {
                        ImplSubject::Trait(tref) => {
                            trait_name = Some(format!("{}", tref.print_only_trait_name()));
                            tref.self_ty()
                        },
                        ImplSubject::Inherent(ty) => {
                            ty
                        }
                    };
                    println!("Self Type: {:?}", self_ty);
                    // apprently this is dangerous, is it in our case?
                    let signature = tcx.fn_sig(defid).skip_binder();
                    println!("Signature: {:?}", signature);

                    let inputs = signature.inputs().iter();
                    let output = signature.output();
                    
                    // Arg Names? We could choose them ourselves if we wanted to..
                    let arg_names = tcx.fn_arg_names(defid);
                    let nr_args = arg_names.len();

                    // let generics = tcx.generics_of(defid);
                    

                    let impl_generics_str = generic_params_str(impl_of_method, &tcx);


                    // Generate result:
                    let mut res = "#[extern_spec]\nimpl".to_string();
                    res.push_str(&format!("{} ", impl_generics_str));
                    if let Some(traitname) = trait_name {
                        res.push_str(&traitname);
                        res.push_str(" for ");
                    }
                    res.push_str(&format!("{} {{\n\tpub fn {}(", self_ty, item_name));
                    for (id,(name, ty)) in arg_names.iter().zip(inputs).enumerate() {
                        let argument = format!("{}: {}", name.as_str(), ty);
                        res.push_str(&argument);
                        if id < nr_args - 1 {
                            res.push_str(", ");
                        }
                    }
                    res.push_str(&format!(") -> {};\n}}", output));

                    println!("Result: {}", res);

                    Some(res)
                }
                None => {
                    // we are apparently dealing with a trait, or even something else
                    None
                }
            }
        }
        // as far as I can tell this is all that's supported for extern_spec
        _ => {
            println!("Apparently not an associated function to some impl block..");
            None
        }
    }
}

pub fn generic_params_str(defid: DefId, tcx: &TyCtxt<'_>) -> String {
    // should receive defid of either an impl block or a function definition.
    // should return a string of the form <'a, S, T> depending on generic parameters.
    let generic_params = tcx.generics_of(defid);
    let traitref = tcx.predicates_of(defid);
    println!("Traitref: {:?}", traitref);

    let mut traitbounds: HashMap<String, String> = HashMap::new();


    for (predicate, _) in traitref.predicates {
        println!("Found predicate of kind: {:?}", predicate.kind());
        let kind: PredicateKind = predicate.kind().skip_binder(); // i don't understand this...
        match kind {
            PredicateKind::Trait(t) => {
                println!("PredicateKind::Trait(t) with t: {:?}", t);
                let traitref = t.trait_ref;
                let self_ty = format!("{}", traitref.self_ty());
                let traitname = format!("{}", traitref.print_only_trait_name());
                println!("self type: {self_ty:?}, traitname: {:?}", traitname);

                let typelist_opt = traitref.substs.try_as_type_list();
                let trait_args = if let Some(typelist) = typelist_opt {
                    if typelist.len() > 1 {
                        let mut trait_args: Vec<String> = vec![];
                        for i in 1..typelist.len() {
                            // the first one is self
                            trait_args.push(format!("{}",typelist[i]));
                        }
                        format!("<{}>", trait_args.join(", "))
                    } else {
                        "".to_string()
                    }
                } else {
                    // throw a warning? I guess this should never happen..
                    "".to_string()
                }; 
                let result = format!("{}{}", traitname, trait_args);
                match traitbounds.get(&self_ty) {
                    None => { traitbounds.insert(self_ty, result); },
                    Some(previous_traits) => {
                        let to_append = format!("{previous_traits} + {result}"); 
                        traitbounds.insert(self_ty, to_append);
                    },
                }
            }
            PredicateKind::Projection(p) => {
                let id = p.projection_ty.item_def_id;
                let parent = tcx.parent(id); // I want the identifier e.g. std::ops::Add
                let parent_traitref: TraitRef = TraitRef::identity(*tcx, parent).skip_binder();
                let parent_identifier = format!("{}", parent_traitref.print_only_trait_name());
                println!("Parent name: {}", parent_identifier);
                let opt_proj_pred = predicate.to_opt_poly_projection_pred().unwrap();


                println!("PredicateKind::Projection(p) with p: {:?}", p);
                println!("Item Name: {}", tcx.opt_item_ident(id).unwrap());
                println!("Trait Def: {}", tcx.opt_item_ident(opt_proj_pred.trait_def_id(*tcx)).unwrap());
            }
            _ => {
                println!("Encountered PredicateKind {:?} but we dont handle it", kind);
            }
        }

    }

    if generic_params.count() > 0 {

        let param_str = generic_params.params
            .iter().map(|param| param.name.as_str())
            .map(|param| if let Some(traitbound) = traitbounds.get(param) {
                    format!("{param}: {traitbound}")
                } else {
                    format!("{param}")
                })
            .collect::<Vec<String>>()
            .join(", ");

        println!("Generics Result: {}", param_str);
        format!("<{}>", param_str)
    } else {
        "".to_string()    
    }
}

