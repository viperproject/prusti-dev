// use crate::encoder::{
//     errors::SpannedEncodingResult,
//     middle::core_proof::{
//         builtin_methods::CallContext, lowerer::Lowerer,
//         predicates::owned::builders::common::predicate_use::PredicateUseBuilder,
//     },
// };

// use vir_crate::{
//     low::{self as vir_low},
//     middle::{
//         self as vir_mid,
//         operations::{const_generics::WithConstArguments, lifetimes::WithLifetimes},
//     },
// };

// pub(in super::super::super::super::super) struct OwnedAliasedUseBuilder<'l, 'p, 'v, 'tcx, G>
// where
//     G: WithLifetimes + WithConstArguments,
// {
//     inner: PredicateUseBuilder<'l, 'p, 'v, 'tcx, G>,
// }

// impl<'l, 'p, 'v, 'tcx, G> OwnedAliasedUseBuilder<'l, 'p, 'v, 'tcx, G>
// where
//     G: WithLifetimes + WithConstArguments,
// {
//     pub(in super::super::super::super::super) fn new(
//         lowerer: &'l mut Lowerer<'p, 'v, 'tcx>,
//         context: CallContext,
//         ty: &'l vir_mid::Type,
//         generics: &'l G,
//         address: vir_low::Expression,
//     ) -> SpannedEncodingResult<Self> {
//         let arguments = vec![address];
//         let inner = PredicateUseBuilder::new(
//             lowerer,
//             "OwnedAliased",
//             context,
//             ty,
//             generics,
//             arguments,
//             Default::default(),
//         )?;
//         Ok(Self { inner })
//     }

//     pub(in super::super::super::super::super) fn build(
//         self,
//     ) -> SpannedEncodingResult<vir_low::Expression> {
//         Ok(self.inner.build())
//     }

//     pub(in super::super::super::super::super) fn add_lifetime_arguments(
//         &mut self,
//     ) -> SpannedEncodingResult<()> {
//         self.inner.add_lifetime_arguments()
//     }

//     pub(in super::super::super::super::super) fn add_const_arguments(
//         &mut self,
//     ) -> SpannedEncodingResult<()> {
//         self.inner.add_const_arguments()
//     }

//     pub(in super::super::super::super::super) fn set_maybe_permission_amount(
//         &mut self,
//         permission_amount: Option<vir_low::Expression>,
//     ) -> SpannedEncodingResult<()> {
//         self.inner.set_maybe_permission_amount(permission_amount)
//     }
// }
