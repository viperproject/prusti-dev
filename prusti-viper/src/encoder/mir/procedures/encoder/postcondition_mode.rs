use vir_crate::common::check_mode::CheckMode;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) struct PostconditionMode {
    is_unsafe_function: bool,
    check_mode: CheckMode,
    no_panic_ensures_postcondition: bool,
    is_checked: bool,
    panic_ensures: bool,
    is_drop_implementation: bool,
}

impl PostconditionMode {
    pub(super) fn regular_exit_on_definition_side(
        is_unsafe_function: bool,
        check_mode: CheckMode,
        no_panic_ensures_postcondition: bool,
        is_drop_implementation: bool,
    ) -> Self {
        Self {
            is_unsafe_function,
            check_mode,
            no_panic_ensures_postcondition,
            panic_ensures: false,
            is_drop_implementation,
            is_checked: false,
        }
    }

    pub(super) fn regular_exit_on_call_side(
        is_unsafe_function: bool,
        check_mode: CheckMode,
        no_panic_ensures_postcondition: bool,
        is_checked: bool,
    ) -> Self {
        Self {
            is_unsafe_function,
            check_mode,
            no_panic_ensures_postcondition,
            panic_ensures: false,
            is_drop_implementation: false,
            is_checked,
        }
    }

    pub(super) fn panic_exit_on_definition_side(
        is_unsafe_function: bool,
        check_mode: CheckMode,
        is_drop_implementation: bool,
    ) -> Self {
        Self {
            is_unsafe_function,
            check_mode,
            no_panic_ensures_postcondition: false,
            panic_ensures: true,
            is_drop_implementation,
            is_checked: false,
        }
    }

    pub(super) fn panic_exit_on_call_side(is_unsafe_function: bool, check_mode: CheckMode) -> Self {
        Self {
            is_unsafe_function,
            check_mode,
            no_panic_ensures_postcondition: false,
            panic_ensures: true,
            is_drop_implementation: false,
            is_checked: false,
        }
    }

    pub(super) fn is_unsafe_function(&self) -> bool {
        self.is_unsafe_function
    }

    fn compute_include_functional_ensures(&self) -> bool {
        self.check_mode.check_specifications()
            || self.no_panic_ensures_postcondition
            || self.is_checked
    }

    fn compute_include_panic_ensures(&self) -> bool {
        self.panic_ensures
    }

    pub(super) fn include_functional_ensures(&self) -> bool {
        let functional = self.compute_include_functional_ensures();
        let panic = self.compute_include_panic_ensures();
        assert!(
            !(functional && panic),
            "Functional and panic postconditions are incompatible: {self:?}"
        );
        functional
    }

    pub(super) fn include_panic_ensures(&self) -> bool {
        let functional = self.compute_include_functional_ensures();
        let panic = self.compute_include_panic_ensures();
        assert!(
            !(functional && panic),
            "Functional and panic postconditions are incompatible: {self:?}"
        );
        panic
    }

    pub(super) fn is_drop_implementation(&self) -> bool {
        self.is_drop_implementation
    }
}
