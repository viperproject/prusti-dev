use prusti_common::config;
use std::{collections::HashMap, fmt};

use super::compiler_info::ProcDef;
use prusti_rustc_interface::{
    hir::{def::DefKind, def_id::DefId},
    middle::ty::{self, Clause, DefIdTree, ImplSubject, PredicateKind, Ty, TyCtxt},
};

// data structure to represent what we want to generate
// since we didnt manage to this with syn etc..

#[derive(Debug)]
enum ExternSpecBlock {
    StandaloneFn {
        parent_chain: String,
        function_sig: FunctionSignature,
    },
    Trait {
        name: String,
        path: String,
        generics: Vec<GenericArg>,
        function_sig: FunctionSignature,
    },
    Impl {
        name: String, // in this case the name also includes
        // the path
        trait_name: Option<String>,
        generics: Vec<GenericArg>,
        function_sig: FunctionSignature,
    },
}

impl ExternSpecBlock {
    fn from_defid(tcx: TyCtxt<'_>, defid: DefId) -> Option<Self> {
        let def_kind = tcx.opt_def_kind(defid)?;
        let signature = FunctionSignature::from_defid(tcx, defid)?;
        match def_kind {
            DefKind::Fn => {
                let parent_chain = get_parent_chain(defid, tcx);
                Some(ExternSpecBlock::StandaloneFn {
                    parent_chain,
                    function_sig: signature,
                })
            }
            DefKind::AssocFn => {
                // this will be None for traits
                let impl_defid_opt = tcx.impl_of_method(defid);
                match impl_defid_opt {
                    Some(impl_defid) => {
                        // function is part of impl block
                        let mut trait_name = None;
                        let impl_subj = tcx.impl_subject(impl_defid);
                        let self_ty = match impl_subj {
                            ImplSubject::Trait(tref) => {
                                trait_name = Some(format!("{}", tref.print_only_trait_name()));
                                tref.self_ty()
                            }
                            ImplSubject::Inherent(ty) => ty,
                        }
                        .to_string();
                        let generics = generic_params(tcx, impl_defid);

                        Some(ExternSpecBlock::Impl {
                            name: self_ty,
                            trait_name,
                            generics,
                            function_sig: signature,
                        })
                    }
                    None => {
                        // function is a Trait (or something else?)
                        // are there other cases for AssocFns?
                        let parent = tcx.opt_parent(defid)?;
                        if tcx.is_trait(parent) {
                            // indeed a trait
                            let traitname = tcx.opt_item_name(parent)?.to_string();
                            let parent_defpath = get_parent_chain(parent, tcx);
                            let trait_params = generic_params(tcx, parent);

                            Some(ExternSpecBlock::Trait {
                                name: traitname,
                                path: parent_defpath,
                                generics: trait_params,
                                function_sig: signature,
                            })
                        } else {
                            None
                        }
                    }
                }
            }
            _ => {
                // another case to be handled?
                None
            }
        }
    }
}

impl fmt::Display for ExternSpecBlock {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ExternSpecBlock::Impl {
                name,
                trait_name,
                generics,
                function_sig,
            } => {
                let generics_str = generic_args_str(&generics, false);
                let where_block = bounds_where_block(&generics);

                write!(f, "#[extern_spec]\nimpl{} ", generics_str)?;
                if let Some(trait_name) = trait_name {
                    write!(f, "{} for ", trait_name)?;
                }
                write!(f, "{} {}{{\n", name, where_block)?;
                let fn_sig = indent(&function_sig.to_string());
                write!(f, "{}\n}}", fn_sig)
            }
            ExternSpecBlock::Trait {
                name,
                path,
                generics,
                function_sig,
            } => {
                let fn_sig = indent(&function_sig.to_string());
                let generics_str = generic_args_str(&generics, false);
                let where_block = bounds_where_block(&generics);
                // do traits specify traitbounds too?
                write!(f, "#[extern_spec({})]\n", path)?;
                write!(f, "trait {}{} {}{{\n", name, generics_str, where_block)?;
                write!(f, "{}\n}}", fn_sig)
            }
            ExternSpecBlock::StandaloneFn {
                parent_chain,
                function_sig,
            } => {
                write!(f, "#[extern_spec({})]\n", parent_chain)?;
                write!(f, "{}", function_sig)
            }
        }
    }
}

#[derive(Debug, Clone)]
struct GenericArg {
    name: String,
    default_value: Option<String>,
    bounds: Vec<TraitBound>,
    projections: HashMap<String, String>,
}

impl fmt::Display for GenericArg {
    // default formatter will include the traitbounds,
    // otherwise just take .name field..
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let bounds_str = traitbounds_string(&self.bounds);
        write!(f, "{}: {}", self.name, bounds_str)
        // for now we ignore defaults since prusti doesnt accept them in
        // some cases..
        // if self.default_value.is_some() {
        //     write!(f, "={}", self.default_value.as_ref().unwrap())?;
        // }
    }
}

// the string for the where clause
fn bounds_where_block(arglist: &Vec<GenericArg>) -> String {
    let bounds_vec = arglist
        .iter()
        .filter(|arg| arg.bounds.len() > 0)
        .map(|arg| format!("\t{}: {}", arg.name, traitbounds_string(&arg.bounds)))
        .collect::<Vec<String>>();
    if bounds_vec.len() > 0 {
        format!("where\n{}\n", bounds_vec.join(",\n"))
    } else {
        "".to_string()
    }
}

fn generic_args_str(arglist: &Vec<GenericArg>, include_bounds: bool) -> String {
    if arglist.len() > 0 {
        let res = arglist
            .iter()
            .map(|genarg| {
                if include_bounds {
                    genarg.to_string()
                } else {
                    genarg.name.clone()
                }
            }) // if we wanted to include defaults this should
            // probably happen here
            .collect::<Vec<String>>()
            .join(", ");
        format!("<{}>", res)
    } else {
        "".to_string()
    }
}

// example result: Sized + PartialEq + Eq
fn traitbounds_string(boundlist: &Vec<TraitBound>) -> String {
    if boundlist.len() > 0 {
        let res = boundlist
            .iter()
            .map(|bound| bound.to_string())
            .collect::<Vec<String>>()
            .join(" + ");
        res
    } else {
        "".to_string()
    }
}

#[derive(Debug, Clone)]
struct TraitBound {
    name: String,
    args: Vec<String>,
}

impl fmt::Display for TraitBound {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)?; // todo
        if self.args.len() >= 1 {
            let args_str = self.args.join(", ");
            write!(f, "<{}>", args_str)?;
        }
        Ok(())
    }
}


#[derive(Debug)]
struct FunctionSignature {
    name: String,
    generics: Vec<GenericArg>,
    arguments: Vec<(String, String)>, // (name, type)
    return_type: Option<String>,
}

impl FunctionSignature {
    fn from_defid(tcx: TyCtxt<'_>, defid: DefId) -> Option<Self> {
        let name = tcx.opt_item_name(defid)?.to_string();
        let sig = tcx.fn_sig(defid).skip_binder();
        let arg_types = sig.inputs().iter();
        let arg_names = tcx.fn_arg_names(defid);
        let output = sig.output();
        let return_type = if output.is_unit() { None } else { Some(output.to_string()) };

        let arguments: Vec<(String, String)> = arg_names
            .iter()
            .zip(arg_types)
            .map(|(name, ty)| (name.to_string(), ty.to_string()))
            .collect();

        let generics = generic_params(tcx, defid);
        Some(Self {
            name,
            generics,
            arguments,
            return_type,
        })
    }

    fn arguments_string(&self) -> String {
        let args = self.arguments
            .iter()
            .map(|(name, ty)| format!("{}: {}", name.to_string(), ty))
            .collect::<Vec<String>>()
            .join(", ");
        format!("({})", args)
    }
}

impl fmt::Display for FunctionSignature {
    // fn<generics>(args) -> output where
    //    bounds;
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let generics_str = generic_args_str(&self.generics, true);
        // let where_block = bounds_where_block(&self.generics);
        let args_str = self.arguments_string();

        write!(f, "fn {}{}{}", self.name, generics_str, args_str)?;
        if let Some(ret_ty) = self.return_type.clone() {
            write!(f, " -> {}", ret_ty)?;
        }
        write!(f, ";")
    }

}

fn generic_params(tcx: TyCtxt<'_>, defid: DefId) -> Vec<GenericArg> {
    let generics = tcx.generics_of(defid);
    let mut generic_params: HashMap<String, GenericArg> = HashMap::new();
    let substs = ty::subst::InternalSubsts::identity_for_item(tcx, defid);

    // first we just collect all generic parameters
    for param in generics.params.iter() {
        let ident = param.name.to_string();
        if ident == "Self" { continue }
        let mut generic_arg = GenericArg {
            name: ident.clone(),
            default_value: None,
            bounds: vec![],
            projections: HashMap::new(),
        };
        let default_opt = param.default_value(tcx);
        if let Some(default_value) = default_opt {
            generic_arg.default_value = Some(format!("{}", default_value.subst(tcx, substs)));
        }

        generic_params.insert(ident, generic_arg);
    }

    // now add traitbounds and default types:
    let predicates = tcx.predicates_of(defid);

    for (predicate, _) in predicates.predicates {
        let kind: PredicateKind = predicate.kind().skip_binder();
        match kind {
            PredicateKind::Clause(Clause::Trait(t)) => {
                let bound_traitref = t.trait_ref;
                let trait_name = tcx.def_path_str(bound_traitref.def_id);
                let self_ty = format!("{}", bound_traitref.self_ty());
                if self_ty == "Self" { continue }
                let trait_args_opt = bound_traitref.substs.try_as_type_list();
                let trait_args = if let Some(typelist) = trait_args_opt {
                    typelist
                        .iter()
                        .skip(1) // the first one is the self type
                        .map(|ty| format!("{}", ty))
                        .collect::<Vec<String>>()
                } else {
                    vec![]
                };
                let bound = TraitBound {
                    name: trait_name,
                    args: trait_args,
                };
                // add this bound to the given type.
                generic_params
                    .get_mut(&self_ty)
                    .unwrap() // is failing appropriate?
                    .bounds
                    .push(bound);
            }
            // not sure if we should even handle this:
            PredicateKind::Clause(Clause::Projection(p)) => {
                let item_id = p.projection_ty.def_id;
                let self_ty = format!("{}", p.projection_ty.self_ty());
                let trait_defid: DefId = p.projection_ty.trait_def_id(tcx);
                let trait_defpath = tcx.def_path_str(trait_defid);

                let item_name = tcx.item_name(item_id);
                
                let projection_term = format!("{}={}", item_name, p.term);
                let genarg = generic_params
                    .get_mut(&self_ty)
                    .unwrap();
                // not sure if this is actually completely correct.
                // can a single generic type have the same traitbound
                // more than once with different arguments?
                // I would imagine yes.. may be a todo
                genarg.projections.insert(trait_defpath, projection_term);
            }
            _ => {}
        }
    }
    
    // handling projections here is simpler than when printing:
    // could not do this directly since projections
    for el in generic_params.values_mut() {
        for tb in &mut el.bounds {
            if let Some(projection_term) = el.projections.get(&tb.name) {
                tb.args.push(projection_term.clone());
            }
        }
    }

    generic_params.values().cloned().collect()
}

pub fn collect_queried_signature(tcx: TyCtxt<'_>, fncalls: &Vec<ProcDef>) -> Option<String> {
    let def_path_str: String = config::query_method_signature()?;
    let existing = fncalls
        .iter()
        .find(|procdef| procdef.name == def_path_str)?;

    // helpers:
    let defid: DefId = existing.defid;
    let extern_spec_block = ExternSpecBlock::from_defid(tcx, defid);
    return extern_spec_block.map(|x| x.to_string());
}
 
fn get_parent_chain(defid: DefId, tcx: TyCtxt<'_>) -> String {
    // let mut parent_opt = tcx.opt_parent(defid);
    // this (above) apparently doesn't work. E.g. for std::ops::Add
    // it will return std::ops::arith which is problematic
    let defpath_str = tcx.def_path_str(defid);
    let mut defpath: Vec<&str> = defpath_str.split("::").collect();
    defpath.pop(); // drop the name itself
    defpath.join("::")
}

fn indent(input: &String) -> String {
    // indent all lines that are not empty by one tab
    let mut res = String::from("\t");
    let len = input.len();
    for (i, c) in input.chars().enumerate() {
        res.push(c);
        if c == '\n' && i != len - 1 {
            // insert a tab after every newline that is not terminating
            // the string
            res.push('\t');
        }
    }
    res
}
