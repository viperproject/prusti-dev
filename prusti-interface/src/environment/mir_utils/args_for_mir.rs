use rustc_index::vec::Idx;
use rustc_middle::mir;
use rustc_middle::ty;

pub trait ArgsForMir<'tcx> {
    fn get_args(&self) -> Vec<(mir::Local, ty::Ty<'tcx>)>;
}

impl<'tcx> ArgsForMir<'tcx> for mir::Body<'tcx> {
    fn get_args(&self) -> Vec<(mir::Local, ty::Ty<'tcx>)> {
        (1..=self.arg_count)
            .map(mir::Local::new)
            .map(|l| (l, self.local_decls[l].clone().ty))
            .collect()
    }
}
