use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::lowerer::{DomainsLowererInterface, Lowerer},
};
use vir_crate::low as vir_low;

pub(in super::super) trait FunctionGasInterface {
    fn function_gas_type(&mut self) -> SpannedEncodingResult<vir_low::Type>;
    fn function_gas_parameter(&mut self) -> SpannedEncodingResult<vir_low::VariableDecl>;
    fn function_no_gas_constant(&mut self) -> SpannedEncodingResult<vir_low::Expression>;
    fn function_gas_constant(
        &mut self,
        gas_amount: u32,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn add_function_gas_level(
        &mut self,
        argument: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression>;
}

impl<'p, 'v: 'p, 'tcx: 'v> FunctionGasInterface for Lowerer<'p, 'v, 'tcx> {
    fn function_gas_type(&mut self) -> SpannedEncodingResult<vir_low::Type> {
        self.domain_type("FunctionGas")
    }

    fn function_gas_parameter(&mut self) -> SpannedEncodingResult<vir_low::VariableDecl> {
        Ok(vir_low::VariableDecl::new(
            "gas$",
            self.function_gas_type()?,
        ))
    }

    fn function_no_gas_constant(&mut self) -> SpannedEncodingResult<vir_low::Expression> {
        let ty = self.function_gas_type()?;
        self.create_domain_func_app(
            "FunctionGas",
            "function_no_gas$",
            Vec::new(),
            ty,
            Default::default(),
        )
    }

    fn function_gas_constant(
        &mut self,
        mut gas_amount: u32,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let mut gas = self.function_no_gas_constant()?;
        while gas_amount > 0 {
            gas = self.add_function_gas_level(gas)?;
            gas_amount -= 1;
        }
        Ok(gas)
    }

    fn add_function_gas_level(
        &mut self,
        argument: vir_low::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let ty = self.function_gas_type()?;
        self.create_domain_func_app(
            "FunctionGas",
            "function_gas_level$",
            vec![argument],
            ty,
            Default::default(),
        )
    }
}
