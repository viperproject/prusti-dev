use prusti_common::config;
use prusti_interface::environment::Environment;
use core::fmt;
use std::collections::HashMap;

use super::ide_info::ProcDef;
use prusti_rustc_interface::{
    hir::{def::DefKind, def_id::DefId},
    middle::ty::{DefIdTree, Generics, ImplSubject, PredicateKind, TraitRef, Ty, TyCtxt},
};

pub fn collect_queried_signatures(env: &Environment<'_>, fncalls: &Vec<ProcDef>) -> Option<String> {
    let def_path_str: String = config::query_method_signature()?;
    println!("\n\n\n\nCollecting Information for Queried Method");
    println!(
        "Got query for external specification template for : {}",
        def_path_str
    );
    let existing = fncalls
        .iter()
        .find(|procdef| procdef.name == def_path_str)?;

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
                        }
                        ImplSubject::Inherent(ty) => ty,
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

                    let (impl_generics_str, _opt_where) = generic_params_str(impl_of_method, &tcx, false);
                    let (fn_generics_str, _opt_where) = generic_params_str(defid, &tcx, false);

                    // Generate result:
                    let mut res = "#[extern_spec]\nimpl".to_string();
                    res.push_str(&format!("{} ", impl_generics_str));
                    if let Some(traitname) = trait_name {
                        res.push_str(&traitname);
                        res.push_str(" for ");
                    }
                    res.push_str(&format!("{} {{\n\tpub fn {}{}(", self_ty, item_name, fn_generics_str));
                    for (id, (name, ty)) in arg_names.iter().zip(inputs).enumerate() {
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

enum GenArguments<'a> {
    GenType(Ty<'a>),
    Projection(String, String),
}

impl<'a> fmt::Display for GenArguments<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::GenType(ty) => {
                write!(f, "{}", ty)
            },
            Self::Projection(item, value) => {
                write!(f, "{}={}", item, value)
            }
        }
    }
}

pub fn generic_params_str(
    defid: DefId, // defid of a function or impl block
    tcx: &TyCtxt<'_>,
    exclude_bounds_to_where: bool, // whether or not trait bounds should be 
                                   // moved into an extra "where" block
) -> (String, Option<String>) {
    // should receive defid of either an impl block or a function definition.
    // should return a string of the form <'a, S, T> depending on generic parameters.
    let generic_params = tcx.generics_of(defid);
    let traitref = tcx.predicates_of(defid);
    println!("Traitref: {:?}", traitref);

    let mut traitbounds: HashMap<String, HashMap<DefId, Vec<GenArguments>>> = HashMap::new();
    // an example entry: impl    <T : Trait1<t1, t2, t3> + Trait2<..>>
    // (or what it represents)

    let mut projections: Vec<(String, DefId, DefId, String)> = vec![];
    for (predicate, _) in traitref.predicates {
        println!("Found predicate of kind: {:?}", predicate.kind());
        let kind: PredicateKind = predicate.kind().skip_binder(); // i don't understand this...
        match kind {
            PredicateKind::Trait(t) => {
                println!("PredicateKind::Trait(t) with t: {:?}", t);
                let traitref = t.trait_ref;
                let self_ty_str = format!("{}", traitref.self_ty());

                let trait_args_opt = traitref.substs.try_as_type_list();
                let trait_args: Vec<GenArguments> = vec![];
                if let Some(typelist) = trait_args_opt {
                    if trait_args.len() > 1 {
                        let mut trait_args: Vec<GenArguments> = vec![];
                        for i in 1..typelist.len() {
                            // the first one is self
                            trait_args.push(GenArguments::GenType(typelist[i]));
                        }
                    }
                }
                match traitbounds.get_mut(&self_ty_str) {
                    None => {
                        traitbounds.insert(self_ty_str, HashMap::from([(traitref.def_id, trait_args)]));
                    }
                    Some(trait_vec) => {
                        trait_vec.insert(traitref.def_id, trait_args);
                    }
                }
            }
            PredicateKind::Projection(p) => {
                // for example, for impl<T: Trait<Output=T>>,
                // - item_id identifies Output,
                // - trait_defid: Trait
                // - term: the type assigned to Ouptut
                // - self_ty: The first T
                //  (not very sure about the last 2)
                let item_id = p.projection_ty.item_def_id;
                let self_ty_str = format!("{}", p.projection_ty.self_ty());

                let trait_defid: DefId = p.projection_ty.trait_def_id(*tcx); // I want the identifier e.g. std::ops::Add
                let term = format!("{}", p.term); // the value to be assigned as default value
                projections.push((self_ty_str, trait_defid, item_id, term));
            }
            _ => {
                println!("Encountered PredicateKind {:?} but we dont handle it", kind);
            }
        }
    }

    // Map the Projections into the other data-structure:
    for (gen_ty_str, trait_id, item_id, value) in projections {
        let bounds_list = traitbounds.get_mut(&gen_ty_str).unwrap();
        let gen_params_list = bounds_list.get_mut(&trait_id).unwrap();
        let item_name = format!("{}", tcx.item_name(item_id));
        gen_params_list.push(GenArguments::Projection(item_name, value));
    }
    // Stringify
    let count = generic_params.params.iter().len();
    // there is a field generic_params.count() but apparently it does not 
    // give us the same value, not sure what it stands for
    if count > 0 {
        let result = generic_params.params  // iterate through all parameters
            .iter()
            .map(|param_ident| {
                let param = param_ident.name.as_str();
                let traitboundmap_opt = traitbounds.get(param);
                if let Some(traitboundmap) = traitboundmap_opt {
                    let trait_list_str = traitboundmap.iter().map(|(trait_id, param_list)| {
                        let trait_str = tcx.def_path_str(*trait_id); 
                        if param_list.len() <= 0 {
                            trait_str
                        } else {
                            let param_str = param_list.iter()
                                .map(|gp| format!("{}", gp))
                                .collect::<Vec<String>>().join(", ");
                            format!("{trait_str}<{param_str}>")
                        }
                    }).collect::<Vec<String>>().join(" + ");
                    format!("{param}:{trait_list_str}")
                } else {
                    param.to_string()
                }
            }).collect::<Vec<String>>().join(", ");
        (format!("<{result}>"), None)
        
    } else {
        ("".to_string(), None)
    }
}
