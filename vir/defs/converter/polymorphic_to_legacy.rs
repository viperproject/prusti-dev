use std::{ 
    fmt,
    collections::HashMap,
};

use super::super::polymorphic;
use super::super::legacy;

pub trait Generic {
    fn substitute(self, map: &HashMap<polymorphic::TypeVar, polymorphic::Type>) -> Self;
}

#[cfg(test)]
mod tests {
    use super::*;

    lazy_static! {
        static ref SUBSTITUTION_MAP : HashMap<polymorphic::TypeVar, polymorphic::Type> = {
            let mut m = HashMap::new();
            m.insert(polymorphic::TypeVar { label: String::from("T") }, polymorphic::Type::Int);
            m.insert(polymorphic::TypeVar { label: String::from("E") }, polymorphic::Type::Bool);
            m.insert(polymorphic::TypeVar { label: String::from("F") }, polymorphic::Type::TypedRef(polymorphic::TypedRef {
                label: String::from("SimpleRef"),
                arguments: vec![],
            }));
            // Substitution into other type vars that have a mapping
            m.insert(polymorphic::TypeVar { label: String::from("G") }, polymorphic::Type::TypedRef(polymorphic::TypedRef {
                label: String::from("ComplexRef"),
                arguments: vec![polymorphic::Type::TypeVar(polymorphic::TypeVar {label: String::from("T") })],
            }));
            // Subsitutition into the same type vars used for substitution
            m.insert(polymorphic::TypeVar { label: String::from("H") }, polymorphic::Type::TypedRef(polymorphic::TypedRef {
                label: String::from("ComplexRef2"),
                arguments: vec![
                    polymorphic::Type::TypeVar(polymorphic::TypeVar {label: String::from("H") }), 
                    polymorphic::Type::Domain(polymorphic::DomainType {
                        label: String::from("ComplexDomain"), 
                        arguments: vec![polymorphic::Type::TypeVar(polymorphic::TypeVar {label: String::from("T")})],
                    })
                ],
            }));
            m
        };
    }

    // Compare the results after substitution with expected value
    fn test<T>(source: T, expected: T, map: &HashMap<polymorphic::TypeVar, polymorphic::Type>) where T: Generic, T: fmt::Debug, T: PartialEq {
        let substituted = source.substitute(map);
        assert_eq!(substituted, expected);
    }

    #[test]
    // source having no type var for substitution
    fn substitution_no_type_var_test() {
        let mut source = polymorphic::Type::Int;
        let mut expected = source.clone();
        test(source, expected, &SUBSTITUTION_MAP);

        source = polymorphic::Type::Bool;
        expected = source.clone();
        test(source, expected, &SUBSTITUTION_MAP);

        source = polymorphic::Type::TypedRef(polymorphic::TypedRef {
            label: String::from("CustomStruct"),
            arguments: vec![polymorphic::Type::Int],
        });
        expected = source.clone();
        test(source, expected, &SUBSTITUTION_MAP);

        source = polymorphic::Type::Domain(polymorphic::DomainType {
            label: String::from("CustomDomain"),
            arguments: vec![],
        });
        expected = source.clone();
        test(source, expected, &SUBSTITUTION_MAP);

        source = polymorphic::Type::Snapshot(polymorphic::SnapshotType {
            label: String::from("CustomSnapshot"),
            arguments: vec![
                polymorphic::Type::Bool, 
                polymorphic::Type::TypedRef(
                    polymorphic::TypedRef {
                        label: String::from("vec"),
                        arguments: vec![polymorphic::Type::Bool],
                    }
                )
            ],
        });
        expected = source.clone();
        test(source, expected, &SUBSTITUTION_MAP);

        source = polymorphic::Type::TypeVar(polymorphic::TypeVar {
            label: String::from("CustomTypeVar"),
        });
        expected = source.clone();
        test(source, expected, &SUBSTITUTION_MAP);
    }

    #[test]
    // source having no matching type var for substitution
    fn substitution_no_matching_type_var_test() {
        let mut source = polymorphic::Type::TypedRef(polymorphic::TypedRef {
            label: String::from("CustomStruct"),
            arguments: vec![polymorphic::Type::TypeVar(polymorphic::TypeVar {
                label: String::from("D"),
            })],
        });
        let mut expected = source.clone();
        test(source, expected, &SUBSTITUTION_MAP);

        source = polymorphic::Type::Domain(polymorphic::DomainType {
            label: String::from("CustomDomain"),
            arguments: vec![
                polymorphic::Type::TypeVar(polymorphic::TypeVar {
                    label: String::from("C"),
                }),
                polymorphic::Type::Int,
                polymorphic::Type::TypeVar(polymorphic::TypeVar {
                    label: String::from("D"),
                }),
            ],
        });
        expected = source.clone();
        test(source, expected, &SUBSTITUTION_MAP);

        source = polymorphic::Type::Snapshot(polymorphic::SnapshotType {
            label: String::from("Custom"),
            arguments: vec![
                polymorphic::Type::Bool,
                polymorphic::Type::TypedRef(
                    polymorphic::TypedRef {
                        label: String::from("vec"),
                        arguments: vec![polymorphic::Type::TypeVar(polymorphic::TypeVar {
                            label: String::from("D")
                        })],
                    }
                )
            ],
        });
        expected = source.clone();
        test(source, expected, &SUBSTITUTION_MAP);
    }

    #[test]
    // successful substitution simple case
    fn substitution_type_var_simple_test() {
        let mut source = polymorphic::Type::TypeVar(polymorphic::TypeVar {
            label: String::from("T"),
        });
        let mut expected = polymorphic::Type::Int;
        test(source, expected, &SUBSTITUTION_MAP);

        source = polymorphic::Type::TypedRef(polymorphic::TypedRef {
            label: String::from("CustomStruct"),
            arguments: vec![
                polymorphic::Type::TypeVar(polymorphic::TypeVar {
                    label: String::from("E"),
                }),
                polymorphic::Type::TypeVar(polymorphic::TypeVar {
                    label: String::from("F"),
                }),
            ],
        });
        expected = polymorphic::Type::TypedRef(polymorphic::TypedRef {
            label: String::from("CustomStruct"),
            arguments: vec![
                polymorphic::Type::Bool,
                polymorphic::Type::TypedRef(polymorphic::TypedRef {
                    label: String::from("SimpleRef"),
                    arguments: vec![],
                })
            ],
        });
        test(source, expected, &SUBSTITUTION_MAP);

        source = polymorphic::Type::Domain(polymorphic::DomainType {
            label: String::from("CustomDomain"),
            arguments: vec![
                polymorphic::Type::TypeVar(polymorphic::TypeVar {
                    label: String::from("E"),
                }),
                polymorphic::Type::TypeVar(polymorphic::TypeVar {
                    label: String::from("F"),
                }),
            ],
        });
        expected = polymorphic::Type::Domain(polymorphic::DomainType {
            label: String::from("CustomDomain"),
            arguments: vec![
                polymorphic::Type::Bool,
                polymorphic::Type::TypedRef(polymorphic::TypedRef {
                    label: String::from("SimpleRef"),
                    arguments: vec![],
                })
            ],
        });
        test(source, expected, &SUBSTITUTION_MAP);

        source = polymorphic::Type::Snapshot(polymorphic::SnapshotType {
            label: String::from("CustomSnapshot"),
            arguments: vec![
                polymorphic::Type::TypeVar(polymorphic::TypeVar {
                    label: String::from("E"),
                }),
                polymorphic::Type::TypeVar(polymorphic::TypeVar {
                    label: String::from("F"),
                }),
            ],
        });
        expected = polymorphic::Type::Snapshot(polymorphic::SnapshotType {
            label: String::from("CustomSnapshot"),
            arguments: vec![
                polymorphic::Type::Bool,
                polymorphic::Type::TypedRef(polymorphic::TypedRef {
                    label: String::from("SimpleRef"),
                    arguments: vec![],
                })
            ],
        });
        test(source, expected, &SUBSTITUTION_MAP);
    }

    #[test]
    // successful substitution more complex case
    fn substitution_type_var_complex_test() {
        // more nested structure
        let mut source = polymorphic::Type::TypedRef(polymorphic::TypedRef {
            label: String::from("CustomStruct"),
            arguments: vec![
                polymorphic::Type::Int,
                polymorphic::Type::Domain(polymorphic::DomainType {
                    label: String::from("CustomDomain"),
                    arguments: vec![
                        polymorphic::Type::TypeVar(polymorphic::TypeVar {
                            label: String::from("E"),
                        }),
                        polymorphic::Type::Snapshot(polymorphic::SnapshotType {
                            label: String::from("CustomSnapshot"),
                            arguments: vec![
                                polymorphic::Type::TypeVar(polymorphic::TypeVar {
                                    label: String::from("F"),
                                }),
                            ]    
                        }),
                    ]
                }),
            ],
        });
        let mut expected = polymorphic::Type::TypedRef(polymorphic::TypedRef {
            label: String::from("CustomStruct"),
            arguments: vec![
                polymorphic::Type::Int,
                polymorphic::Type::Domain(polymorphic::DomainType {
                    label: String::from("CustomDomain"),
                    arguments: vec![
                        polymorphic::Type::Bool,
                        polymorphic::Type::Snapshot(polymorphic::SnapshotType {
                            label: String::from("CustomSnapshot"),
                            arguments: vec![
                                polymorphic::Type::TypedRef(polymorphic::TypedRef {
                                    label: String::from("SimpleRef"),
                                    arguments: vec![],
                                }),
                            ]    
                        }),
                    ]
                }),
            ],
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // structures having type vars after substitution
        let mut source = polymorphic::Type::TypedRef(polymorphic::TypedRef {
            label: String::from("CustomStruct"),
            arguments: vec![
                polymorphic::Type::TypeVar(polymorphic::TypeVar {
                    label: String::from("G"),
                }),
                polymorphic::Type::Domain(polymorphic::DomainType {
                    label: String::from("CustomDomain"),
                    arguments: vec![
                        polymorphic::Type::TypeVar(polymorphic::TypeVar {
                            label: String::from("H"),
                        }),
                        polymorphic::Type::Snapshot(polymorphic::SnapshotType {
                            label: String::from("CustomSnapshot"),
                            arguments: vec![
                                polymorphic::Type::TypeVar(polymorphic::TypeVar {
                                    label: String::from("F"),
                                }),
                            ]    
                        }),
                    ]
                }),
            ],
        });
        let mut expected = polymorphic::Type::TypedRef(polymorphic::TypedRef {
            label: String::from("CustomStruct"),
            arguments: vec![
                polymorphic::Type::TypedRef(polymorphic::TypedRef {
                    label: String::from("ComplexRef"),
                    arguments: vec![polymorphic::Type::TypeVar(polymorphic::TypeVar {label: String::from("T") })],
                }),
                polymorphic::Type::Domain(polymorphic::DomainType {
                    label: String::from("CustomDomain"),
                    arguments: vec![
                        polymorphic::Type::TypedRef(polymorphic::TypedRef {
                            label: String::from("ComplexRef2"),
                            arguments: vec![
                                polymorphic::Type::TypeVar(polymorphic::TypeVar {label: String::from("H") }), 
                                polymorphic::Type::Domain(polymorphic::DomainType {
                                    label: String::from("ComplexDomain"), 
                                    arguments: vec![polymorphic::Type::TypeVar(polymorphic::TypeVar {label: String::from("T")})],
                                })
                            ],
                        }),
                        polymorphic::Type::Snapshot(polymorphic::SnapshotType {
                            label: String::from("CustomSnapshot"),
                            arguments: vec![
                                polymorphic::Type::TypedRef(polymorphic::TypedRef {
                                    label: String::from("SimpleRef"),
                                    arguments: vec![],
                                }),
                            ]    
                        }),
                    ]
                }),
            ],
        });
        test(source, expected, &SUBSTITUTION_MAP);
    }

    #[test]
    // successful substitution within LocalVar
    fn substitution_type_var_local_var_test() {
        let source = polymorphic::LocalVar {
            name: String::from("_v1"),
            typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                label: String::from("T"),
            }),
        };
        let expected = polymorphic::LocalVar {
            name: String::from("_v1"),
            typ: polymorphic::Type::Int,
        };
        test(source, expected, &SUBSTITUTION_MAP);
    }

    #[test]
    // successful substitution within Field
    fn substitution_type_var_field_test() {
        let source = polymorphic::Field {
            name: String::from("_f1"),
            typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                label: String::from("T"),
            }),
        };
        let expected = polymorphic::Field {
            name: String::from("_f1"),
            typ: polymorphic::Type::Int,
        };
        test(source, expected, &SUBSTITUTION_MAP);
    }

    #[test]
    // successful substitution within Expr, going over all variants
    fn substitution_type_var_expr_test() {
        // dummy position for convenient copying
        let position = polymorphic::Position::new(1, 2, 3);

        // Local
        let mut source = polymorphic::Expr::Local(polymorphic::Local {
            variable: polymorphic::LocalVar {
                name: String::from("_v1"),
                typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                    label: String::from("T"),
                }),
            },
            position: position.clone(),
        });
        let mut expected = polymorphic::Expr::Local(polymorphic::Local {
            variable: polymorphic::LocalVar {
                name: String::from("_v1"),
                typ: polymorphic::Type::Int,
            },
            position: position.clone(),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // Variant
        source = polymorphic::Expr::Variant(polymorphic::Variant {
            base: Box::new(
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v1"),
                        typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                            label: String::from("T"),
                        }),
                    },
                    position: position.clone(),
            })),
            variant_index: polymorphic::Field {
                name: String::from("_f1"),
                typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                    label: String::from("T"),
                }),
            },
            position: position.clone(),
        });
        expected = polymorphic::Expr::Variant(polymorphic::Variant {
            base: Box::new(
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v1"),
                        typ: polymorphic::Type::Int,
                    },
                    position: position.clone(),
            })),
            variant_index: polymorphic::Field {
                name: String::from("_f1"),
                typ: polymorphic::Type::Int,
            },
            position: position.clone(),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // Field
        source = polymorphic::Expr::Field(polymorphic::FieldExpr {
            base: Box::new(
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v1"),
                        typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                            label: String::from("T"),
                        }),
                    },
                    position: position.clone(),
            })),
            field: polymorphic::Field {
                name: String::from("_f1"),
                typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                    label: String::from("T"),
                }),
            },
            position: position.clone(),
        });
        expected = polymorphic::Expr::Field(polymorphic::FieldExpr {
            base: Box::new(
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v1"),
                        typ: polymorphic::Type::Int,
                    },
                    position: position.clone(),
            })),
            field: polymorphic::Field {
                name: String::from("_f1"),
                typ: polymorphic::Type::Int,
            },
            position: position.clone(),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // AddrOf
        source = polymorphic::Expr::AddrOf(polymorphic::AddrOf {
            base: Box::new(
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v1"),
                        typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                            label: String::from("T"),
                        }),
                    },
                    position: position.clone(),
            })),
            addr_type: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                label: String::from("E"),
            }),
            position: position.clone(),
        });
        expected = polymorphic::Expr::AddrOf(polymorphic::AddrOf {
            base: Box::new(
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v1"),
                        typ: polymorphic::Type::Int,
                    },
                    position: position.clone(),
            })),
            addr_type: polymorphic::Type::Bool,
            position: position.clone(),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // LabelledOld
        source = polymorphic::Expr::LabelledOld(polymorphic::LabelledOld {
            label: String::from("l1"),
            base: Box::new(
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v1"),
                        typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                            label: String::from("T"),
                        }),
                    },
                    position: position.clone(),
            })),
            position: position.clone(),
        });
        expected = polymorphic::Expr::LabelledOld(polymorphic::LabelledOld {
            label: String::from("l1"),
            base: Box::new(
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v1"),
                        typ: polymorphic::Type::Int,
                    },
                    position: position.clone(),
            })),
            position: position.clone(),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // Const
        source = polymorphic::Expr::Const(polymorphic::ConstExpr {
            value: polymorphic::Const::Int(123),
            position: position.clone(),
        });
        expected = polymorphic::Expr::Const(polymorphic::ConstExpr {
            value: polymorphic::Const::Int(123),
            position: position.clone(),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // MagicWand
        source = polymorphic::Expr::MagicWand(polymorphic::MagicWand {
            left: Box::new(
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_left"),
                        typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                            label: String::from("T"),
                        }),
                    },
                    position: position.clone(),
            })),
            right: Box::new(
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_right"),
                        typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                            label: String::from("E"),
                        }),
                    },
                    position: position.clone(),
            })),
            borrow: Some(polymorphic::Borrow(123)),
            position: position.clone(),
        });
        expected = polymorphic::Expr::MagicWand(polymorphic::MagicWand {
            left: Box::new(
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_left"),
                        typ: polymorphic::Type::Int,
                    },
                    position: position.clone(),
            })),
            right: Box::new(
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_right"),
                        typ: polymorphic::Type::Bool,
                    },
                    position: position.clone(),
            })),
            borrow: Some(polymorphic::Borrow(123)),
            position: position.clone(),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // PredicateAccessPredicate
        source = polymorphic::Expr::PredicateAccessPredicate(polymorphic::PredicateAccessPredicate {
            predicate_name: String::from("_p1"),
            argument: Box::new(
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v1"),
                        typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                            label: String::from("T"),
                        }),
                    },
                    position: position.clone(),
            })),
            permission: polymorphic::PermAmount::Read,
            position: position.clone(),
        });
        expected = polymorphic::Expr::PredicateAccessPredicate(polymorphic::PredicateAccessPredicate {
            predicate_name: String::from("_p1"),
            argument: Box::new(
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v1"),
                        typ: polymorphic::Type::Int,
                    },
                    position: position.clone(),
            })),
            permission: polymorphic::PermAmount::Read,
            position: position.clone(),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // FieldAccessPredicate
        source = polymorphic::Expr::FieldAccessPredicate(polymorphic::FieldAccessPredicate {
            base: Box::new(
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v1"),
                        typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                            label: String::from("T"),
                        }),
                    },
                    position: position.clone(),
            })),
            permission: polymorphic::PermAmount::Read,
            position: position.clone(),
        });
        expected = polymorphic::Expr::FieldAccessPredicate(polymorphic::FieldAccessPredicate {
            base: Box::new(
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v1"),
                        typ: polymorphic::Type::Int,
                    },
                    position: position.clone(),
            })),
            permission: polymorphic::PermAmount::Read,
            position: position.clone(),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // UnaryOp
        source = polymorphic::Expr::UnaryOp(polymorphic::UnaryOp {
            op_kind: polymorphic::UnaryOpKind::Minus,
            argument: Box::new(
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v1"),
                        typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                            label: String::from("T"),
                        }),
                    },
                    position: position.clone(),
            })),
            position: position.clone(),
        });
        expected = polymorphic::Expr::UnaryOp(polymorphic::UnaryOp {
            op_kind: polymorphic::UnaryOpKind::Minus,
            argument: Box::new(
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v1"),
                        typ: polymorphic::Type::Int,
                    },
                    position: position.clone(),
            })),
            position: position.clone(),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // BinOp
        source = polymorphic::Expr::BinOp(polymorphic::BinOp {
            op_kind: polymorphic::BinOpKind::Mul,
            left: Box::new(
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v1"),
                        typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                            label: String::from("T"),
                        }),
                    },
                    position: position.clone(),
            })),
            right: Box::new(
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v2"),
                        typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                            label: String::from("E"),
                        }),
                    },
                    position: position.clone(),
            })),
            position: position.clone(),
        });
        expected = polymorphic::Expr::BinOp(polymorphic::BinOp {
            op_kind: polymorphic::BinOpKind::Mul,
            left: Box::new(
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v1"),
                        typ: polymorphic::Type::Int,
                    },
                    position: position.clone(),
            })),
            right: Box::new(
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v2"),
                        typ: polymorphic::Type::Bool,
                    },
                    position: position.clone(),
            })),
            position: position.clone(),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // ContainerOp
        source = polymorphic::Expr::ContainerOp(polymorphic::ContainerOp {
            op_kind: polymorphic::ContainerOpKind::SeqConcat,
            left: Box::new(
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v1"),
                        typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                            label: String::from("T"),
                        }),
                    },
                    position: position.clone(),
            })),
            right: Box::new(
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v2"),
                        typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                            label: String::from("E"),
                        }),
                    },
                    position: position.clone(),
            })),
            position: position.clone(),
        });
        expected = polymorphic::Expr::ContainerOp(polymorphic::ContainerOp {
            op_kind: polymorphic::ContainerOpKind::SeqConcat,
            left: Box::new(
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v1"),
                        typ: polymorphic::Type::Int,
                    },
                    position: position.clone(),
            })),
            right: Box::new(
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v2"),
                        typ: polymorphic::Type::Bool,
                    },
                    position: position.clone(),
            })),
            position: position.clone(),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // Seq
        source = polymorphic::Expr::Seq(polymorphic::Seq {
            typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                label: String::from("T"),
            }),
            elements: vec![
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v1"),
                        typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                            label: String::from("T"),
                        }),
                    },
                    position: position.clone(),
                }),
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v2"),
                        typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                            label: String::from("E"),
                        }),
                    },
                    position: position.clone(),
                }),
            ],
            position: position.clone(),
        });
        expected = polymorphic::Expr::Seq(polymorphic::Seq {
            typ: polymorphic::Type::Int,
            elements: vec![
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v1"),
                        typ: polymorphic::Type::Int,
                    },
                    position: position.clone(),
                }),
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v2"),
                        typ: polymorphic::Type::Bool,
                    },
                    position: position.clone(),
                }),
            ],
            position: position.clone(),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // Unfolding
        source = polymorphic::Expr::Unfolding(polymorphic::Unfolding {
            predicate_name: String::from("p1"),
            arguments: vec![
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v1"),
                        typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                            label: String::from("T"),
                        }),
                    },
                    position: position.clone(),
                }),
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v2"),
                        typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                            label: String::from("E"),
                        }),
                    },
                    position: position.clone(),
                }),
            ],
            base: Box::new(polymorphic::Expr::Local(polymorphic::Local {
                variable: polymorphic::LocalVar {
                    name: String::from("_v3"),
                    typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                        label: String::from("T"),
                    }),
                },
                position: position.clone(),
            })),
            permission: polymorphic::PermAmount::Write,
            variant: Some(polymorphic::EnumVariantIndex::new(String::from("evi"))),
            position: position.clone(),
        });
        expected = polymorphic::Expr::Unfolding(polymorphic::Unfolding {
            predicate_name: String::from("p1"),
            arguments: vec![
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v1"),
                        typ: polymorphic::Type::Int,
                    },
                    position: position.clone(),
                }),
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v2"),
                        typ: polymorphic::Type::Bool,
                    },
                    position: position.clone(),
                }),
            ],
            base: Box::new(polymorphic::Expr::Local(polymorphic::Local {
                variable: polymorphic::LocalVar {
                    name: String::from("_v3"),
                    typ: polymorphic::Type::Int,
                },
                position: position.clone(),
            })),
            permission: polymorphic::PermAmount::Write,
            variant: Some(polymorphic::EnumVariantIndex::new(String::from("evi"))),
            position: position.clone(),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // Cond
        source = polymorphic::Expr::Cond(polymorphic::Cond {
            guard: Box::new(polymorphic::Expr::Local(polymorphic::Local {
                variable: polymorphic::LocalVar {
                    name: String::from("_v1"),
                    typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                        label: String::from("T"),
                    }),
                },
                position: position.clone(),
            })),
            then_expr: Box::new( polymorphic::Expr::Local(polymorphic::Local {
                variable: polymorphic::LocalVar {
                    name: String::from("_v2"),
                    typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                        label: String::from("E"),
                    }),
                },
                position: position.clone(),
            })),
            else_expr: Box::new(polymorphic::Expr::Local(polymorphic::Local {
                variable: polymorphic::LocalVar {
                    name: String::from("_v3"),
                    typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                        label: String::from("T"),
                    }),
                },
                position: position.clone(),
            })),
            position: position.clone(),
        });
        expected = polymorphic::Expr::Cond(polymorphic::Cond {
            guard: Box::new(polymorphic::Expr::Local(polymorphic::Local {
                variable: polymorphic::LocalVar {
                    name: String::from("_v1"),
                    typ: polymorphic::Type::Int,
                },
                position: position.clone(),
            })),
            then_expr: Box::new( polymorphic::Expr::Local(polymorphic::Local {
                variable: polymorphic::LocalVar {
                    name: String::from("_v2"),
                    typ: polymorphic::Type::Bool,
                },
                position: position.clone(),
            })),
            else_expr: Box::new(polymorphic::Expr::Local(polymorphic::Local {
                variable: polymorphic::LocalVar {
                    name: String::from("_v3"),
                    typ: polymorphic::Type::Int,
                },
                position: position.clone(),
            })),
            position: position.clone(),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // ForAll
        source = polymorphic::Expr::ForAll(polymorphic::ForAll {
            variables: vec![
                polymorphic::LocalVar {
                    name: String::from("_v1"),
                    typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                        label: String::from("T"),
                    }),
                },
                polymorphic::LocalVar {
                    name: String::from("_v2"),
                    typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                        label: String::from("E"),
                    }),
                },
            ],
            triggers: vec![
                polymorphic::Trigger::new(
                    vec![
                        polymorphic::Expr::Local(polymorphic::Local {
                            variable: polymorphic::LocalVar {
                                name: String::from("_v3"),
                                typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                                    label: String::from("T"),
                                }),
                            },
                            position: position.clone(),
                        }),
                        polymorphic::Expr::Local(polymorphic::Local {
                            variable: polymorphic::LocalVar {
                                name: String::from("_v4"),
                                typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                                    label: String::from("E"),
                                }),
                            },
                            position: position.clone(),
                        })
                    ]
                )
            ],
            body: Box::new(polymorphic::Expr::Local(polymorphic::Local {
                variable: polymorphic::LocalVar {
                    name: String::from("_v5"),
                    typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                        label: String::from("T"),
                    }),
                },
                position: position.clone(),
            })),
            position: position.clone(),
        });
        expected = polymorphic::Expr::ForAll(polymorphic::ForAll {
            variables: vec![
                polymorphic::LocalVar {
                    name: String::from("_v1"),
                    typ: polymorphic::Type::Int,
                },
                polymorphic::LocalVar {
                    name: String::from("_v2"),
                    typ: polymorphic::Type::Bool,
                },
            ],
            triggers: vec![
                polymorphic::Trigger::new(
                    vec![
                        polymorphic::Expr::Local(polymorphic::Local {
                            variable: polymorphic::LocalVar {
                                name: String::from("_v3"),
                                typ: polymorphic::Type::Int,
                            },
                            position: position.clone(),
                        }),
                        polymorphic::Expr::Local(polymorphic::Local {
                            variable: polymorphic::LocalVar {
                                name: String::from("_v4"),
                                typ: polymorphic::Type::Bool,
                            },
                            position: position.clone(),
                        })
                    ]
                )
            ],
            body: Box::new(polymorphic::Expr::Local(polymorphic::Local {
                variable: polymorphic::LocalVar {
                    name: String::from("_v5"),
                    typ: polymorphic::Type::Int,
                },
                position: position.clone(),
            })),
            position: position.clone(),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // Exists
        source = polymorphic::Expr::Exists(polymorphic::Exists {
            variables: vec![
                polymorphic::LocalVar {
                    name: String::from("_v1"),
                    typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                        label: String::from("T"),
                    }),
                },
                polymorphic::LocalVar {
                    name: String::from("_v2"),
                    typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                        label: String::from("E"),
                    }),
                },
            ],
            triggers: vec![
                polymorphic::Trigger::new(
                    vec![
                        polymorphic::Expr::Local(polymorphic::Local {
                            variable: polymorphic::LocalVar {
                                name: String::from("_v3"),
                                typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                                    label: String::from("T"),
                                }),
                            },
                            position: position.clone(),
                        }),
                        polymorphic::Expr::Local(polymorphic::Local {
                            variable: polymorphic::LocalVar {
                                name: String::from("_v4"),
                                typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                                    label: String::from("E"),
                                }),
                            },
                            position: position.clone(),
                        })
                    ]
                )
            ],
            body: Box::new(polymorphic::Expr::Local(polymorphic::Local {
                variable: polymorphic::LocalVar {
                    name: String::from("_v5"),
                    typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                        label: String::from("T"),
                    }),
                },
                position: position.clone(),
            })),
            position: position.clone(),
        });
        expected = polymorphic::Expr::Exists(polymorphic::Exists {
            variables: vec![
                polymorphic::LocalVar {
                    name: String::from("_v1"),
                    typ: polymorphic::Type::Int,
                },
                polymorphic::LocalVar {
                    name: String::from("_v2"),
                    typ: polymorphic::Type::Bool,
                },
            ],
            triggers: vec![
                polymorphic::Trigger::new(
                    vec![
                        polymorphic::Expr::Local(polymorphic::Local {
                            variable: polymorphic::LocalVar {
                                name: String::from("_v3"),
                                typ: polymorphic::Type::Int,
                            },
                            position: position.clone(),
                        }),
                        polymorphic::Expr::Local(polymorphic::Local {
                            variable: polymorphic::LocalVar {
                                name: String::from("_v4"),
                                typ: polymorphic::Type::Bool,
                            },
                            position: position.clone(),
                        })
                    ]
                )
            ],
            body: Box::new(polymorphic::Expr::Local(polymorphic::Local {
                variable: polymorphic::LocalVar {
                    name: String::from("_v5"),
                    typ: polymorphic::Type::Int,
                },
                position: position.clone(),
            })),
            position: position.clone(),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // LetExpr
        source = polymorphic::Expr::LetExpr(polymorphic::LetExpr {
            variable: polymorphic::LocalVar {
                name: String::from("_v1"),
                typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                    label: String::from("T"),
                }),
            },
            def:Box::new(polymorphic::Expr::Local(polymorphic::Local {
                variable: polymorphic::LocalVar {
                    name: String::from("_v2"),
                    typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                        label: String::from("E"),
                    }),
                },
                position: position.clone(),
            })),
            body: Box::new(polymorphic::Expr::Local(polymorphic::Local {
                variable: polymorphic::LocalVar {
                    name: String::from("_v3"),
                    typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                        label: String::from("T"),
                    }),
                },
                position: position.clone(),
            })),
            position: position.clone(),
        });
        expected = polymorphic::Expr::LetExpr(polymorphic::LetExpr {
            variable: polymorphic::LocalVar {
                name: String::from("_v1"),
                typ: polymorphic::Type::Int,
            },
            def:Box::new(polymorphic::Expr::Local(polymorphic::Local {
                variable: polymorphic::LocalVar {
                    name: String::from("_v2"),
                    typ: polymorphic::Type::Bool,
                },
                position: position.clone(),
            })),
            body: Box::new(polymorphic::Expr::Local(polymorphic::Local {
                variable: polymorphic::LocalVar {
                    name: String::from("_v3"),
                    typ: polymorphic::Type::Int,
                },
                position: position.clone(),
            })),
            position: position.clone(),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // FuncApp
        source = polymorphic::Expr::FuncApp(polymorphic::FuncApp {
            function_name: String::from("f1"),
            arguments: vec![
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v2"),
                        typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                            label: String::from("E"),
                        }),
                    },
                    position: position.clone(),
                }),
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v3"),
                        typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                            label: String::from("T"),
                        }),
                    },
                    position: position.clone(),
                }),
            ],
            formal_arguments: vec![
                polymorphic::LocalVar {
                    name: String::from("_v4"),
                    typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                        label: String::from("E"),
                    }),
                },
                polymorphic::LocalVar {
                    name: String::from("_v5"),
                    typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                        label: String::from("T"),
                    }),
                },
            ],
            return_type: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                label: String::from("E"),
            }),
            position: position.clone(),
        });
        expected = polymorphic::Expr::FuncApp(polymorphic::FuncApp {
            function_name: String::from("f1"),
            arguments: vec![
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v2"),
                        typ: polymorphic::Type::Bool,
                    },
                    position: position.clone(),
                }),
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v3"),
                        typ: polymorphic::Type::Int,
                    },
                    position: position.clone(),
                }),
            ],
            formal_arguments: vec![
                polymorphic::LocalVar {
                    name: String::from("_v4"),
                    typ: polymorphic::Type::Bool,
                },
                polymorphic::LocalVar {
                    name: String::from("_v5"),
                    typ: polymorphic::Type::Int,
                },
            ],
            return_type: polymorphic::Type::Bool,
            position: position.clone(),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // DomainFuncApp
        source = polymorphic::Expr::DomainFuncApp(polymorphic::DomainFuncApp {
            domain_function: polymorphic::DomainFunc {
                name: String::from("df1"),
                formal_args: vec![
                    polymorphic::LocalVar {
                        name: String::from("_v2"),
                        typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                            label: String::from("E"),
                        }),
                    },
                    polymorphic::LocalVar {
                        name: String::from("_v3"),
                        typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                            label: String::from("T"),
                        }),
                    },
                ],
                return_type: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                    label: String::from("T"),
                }),
                unique: false,
                domain_name: String::from("dn1"),
            },
            arguments: vec![
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v2"),
                        typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                            label: String::from("E"),
                        }),
                    },
                    position: position.clone(),
                }),
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v3"),
                        typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                            label: String::from("T"),
                        }),
                    },
                    position: position.clone(),
                }),
            ],
            position: position.clone(),
        });
        expected = polymorphic::Expr::DomainFuncApp(polymorphic::DomainFuncApp {
            domain_function: polymorphic::DomainFunc {
                name: String::from("df1"),
                formal_args: vec![
                    polymorphic::LocalVar {
                        name: String::from("_v2"),
                        typ: polymorphic::Type::Bool,
                    },
                    polymorphic::LocalVar {
                        name: String::from("_v3"),
                        typ: polymorphic::Type::Int,
                    },
                ],
                return_type: polymorphic::Type::Int,
                unique: false,
                domain_name: String::from("dn1"),
            },
            arguments: vec![
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v2"),
                        typ: polymorphic::Type::Bool,
                    },
                    position: position.clone(),
                }),
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v3"),
                        typ: polymorphic::Type::Int,
                    },
                    position: position.clone(),
                }),
            ],
            position: position.clone(),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // InhaleExhale
        source = polymorphic::Expr::InhaleExhale(polymorphic::InhaleExhale {
            inhale_expr: Box::new(
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v1"),
                        typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                            label: String::from("T"),
                        }),
                    },
                    position: position.clone(),
            })),
            exhale_expr: Box::new(
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v2"),
                        typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                            label: String::from("E"),
                        }),
                    },
                    position: position.clone(),
            })),
            position: position.clone(),
        });
        expected = polymorphic::Expr::InhaleExhale(polymorphic::InhaleExhale {
            inhale_expr: Box::new(
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v1"),
                        typ: polymorphic::Type::Int,
                    },
                    position: position.clone(),
            })),
            exhale_expr: Box::new(
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v2"),
                        typ: polymorphic::Type::Bool,
                    },
                    position: position.clone(),
            })),
            position: position.clone(),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // Downcast
        source = polymorphic::Expr::Downcast(polymorphic::DowncastExpr {
            base: Box::new(
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v1"),
                        typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                            label: String::from("T"),
                        }),
                    },
                    position: position.clone(),
            })),
            enum_place: Box::new(
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v2"),
                        typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                            label: String::from("E"),
                        }),
                    },
                    position: position.clone(),
            })),
            field: polymorphic::Field {
                name: String::from("f1"),
                typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                    label: String::from("E"),
                }),
            },
        });
        expected = polymorphic::Expr::Downcast(polymorphic::DowncastExpr {
            base: Box::new(
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v1"),
                        typ: polymorphic::Type::Int,
                    },
                    position: position.clone(),
            })),
            enum_place: Box::new(
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v2"),
                        typ: polymorphic::Type::Bool,
                    },
                    position: position.clone(),
            })),
            field: polymorphic::Field {
                name: String::from("f1"),
                typ: polymorphic::Type::Bool,
            },
        });
        test(source, expected, &SUBSTITUTION_MAP);
    }

    #[test]
    // successful substitution within Stmt, going over all variants
    fn substitution_type_var_stmt_test() {
        // dummy position for convenient copying
        let position = polymorphic::Position::new(1, 2, 3);

        // Comment
        let mut source = polymorphic::Stmt::Comment(polymorphic::Comment {
            comment: String::from("c1"),
        });
        let mut expected = polymorphic::Stmt::Comment(polymorphic::Comment {
            comment: String::from("c1"),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // Label
        source = polymorphic::Stmt::Label(polymorphic::Label {
            label: String::from("c1"),
        });
        expected = polymorphic::Stmt::Label(polymorphic::Label {
            label: String::from("c1"),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // Inhale
        source = polymorphic::Stmt::Inhale(polymorphic::Inhale {
            expr: polymorphic::Expr::Local(polymorphic::Local {
                variable: polymorphic::LocalVar {
                    name: String::from("_v1"),
                    typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                        label: String::from("T"),
                    }),
                },
                position: position.clone(),
            }),
        });
        expected = polymorphic::Stmt::Inhale(polymorphic::Inhale {
            expr: polymorphic::Expr::Local(polymorphic::Local {
                variable: polymorphic::LocalVar {
                    name: String::from("_v1"),
                    typ: polymorphic::Type::Int,
                },
                position: position.clone(),
            }),
        });
        test(source, expected, &SUBSTITUTION_MAP);


        // Exhale
        source = polymorphic::Stmt::Exhale(polymorphic::Exhale {
            expr: polymorphic::Expr::Local(polymorphic::Local {
                variable: polymorphic::LocalVar {
                    name: String::from("_v1"),
                    typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                        label: String::from("T"),
                    }),
                },
                position: position.clone(),
            }),
            position: position.clone(),
        });
        expected = polymorphic::Stmt::Exhale(polymorphic::Exhale {
            expr: polymorphic::Expr::Local(polymorphic::Local {
                variable: polymorphic::LocalVar {
                    name: String::from("_v1"),
                    typ: polymorphic::Type::Int,
                },
                position: position.clone(),
            }),
            position: position.clone(),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // Assert
        source = polymorphic::Stmt::Assert(polymorphic::Assert {
            expr: polymorphic::Expr::Local(polymorphic::Local {
                variable: polymorphic::LocalVar {
                    name: String::from("_v1"),
                    typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                        label: String::from("T"),
                    }),
                },
                position: position.clone(),
            }),
            position: position.clone(),
        });
        expected = polymorphic::Stmt::Assert(polymorphic::Assert {
            expr: polymorphic::Expr::Local(polymorphic::Local {
                variable: polymorphic::LocalVar {
                    name: String::from("_v1"),
                    typ: polymorphic::Type::Int,
                },
                position: position.clone(),
            }),
            position: position.clone(),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // MethodCall
        source = polymorphic::Stmt::MethodCall(polymorphic::MethodCall {
            method_name: String::from("m1"),
            arguments: vec![
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v2"),
                        typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                            label: String::from("E"),
                        }),
                    },
                    position: position.clone(),
                }),
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v3"),
                        typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                            label: String::from("T"),
                        }),
                    },
                    position: position.clone(),
                }),
            ],
            targets: vec![
                polymorphic::LocalVar {
                    name: String::from("_v4"),
                    typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                        label: String::from("E"),
                    }),
                },
                polymorphic::LocalVar {
                    name: String::from("_v5"),
                    typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                        label: String::from("T"),
                    }),
                },
            ],
        });
        expected = polymorphic::Stmt::MethodCall(polymorphic::MethodCall {
            method_name: String::from("m1"),
            arguments: vec![
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v2"),
                        typ: polymorphic::Type::Bool,
                    },
                    position: position.clone(),
                }),
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v3"),
                        typ: polymorphic::Type::Int,
                    },
                    position: position.clone(),
                }),
            ],
            targets: vec![
                polymorphic::LocalVar {
                    name: String::from("_v4"),
                    typ: polymorphic::Type::Bool,
                },
                polymorphic::LocalVar {
                    name: String::from("_v5"),
                    typ: polymorphic::Type::Int,
                },
            ],
        });
        test(source, expected, &SUBSTITUTION_MAP);

       // Assign
        source = polymorphic::Stmt::Assign(polymorphic::Assign {
            target: polymorphic::Expr::Local(polymorphic::Local {
                variable: polymorphic::LocalVar {
                    name: String::from("_v1"),
                    typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                        label: String::from("E"),
                    }),
                },
                position: position.clone(),
            }),
            source: polymorphic::Expr::Local(polymorphic::Local {
                variable: polymorphic::LocalVar {
                    name: String::from("_v2"),
                    typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                        label: String::from("T"),
                    }),
                },
                position: position.clone(),
            }),
            kind: polymorphic::AssignKind::SharedBorrow(polymorphic::Borrow(123)),
        });
        expected = polymorphic::Stmt::Assign(polymorphic::Assign {
            target: polymorphic::Expr::Local(polymorphic::Local {
                variable: polymorphic::LocalVar {
                    name: String::from("_v1"),
                    typ: polymorphic::Type::Bool,
                },
                position: position.clone(),
            }),
            source: polymorphic::Expr::Local(polymorphic::Local {
                variable: polymorphic::LocalVar {
                    name: String::from("_v2"),
                    typ: polymorphic::Type::Int,
                },
                position: position.clone(),
            }),
            kind: polymorphic::AssignKind::SharedBorrow(polymorphic::Borrow(123)),
        });
        test(source, expected, &SUBSTITUTION_MAP);

       // Fold
        source = polymorphic::Stmt::Fold(polymorphic::Fold {
            predicate_name: String::from("p1"),
            arguments: vec![
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v2"),
                        typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                            label: String::from("E"),
                        }),
                    },
                    position: position.clone(),
                }),
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v3"),
                        typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                            label: String::from("T"),
                        }),
                    },
                    position: position.clone(),
                }),
            ],
            permission: polymorphic::PermAmount::Write,
            enum_variant: Some(polymorphic::EnumVariantIndex::new(String::from("evi"))),
            position: position.clone(),
        });
        expected = polymorphic::Stmt::Fold(polymorphic::Fold {
            predicate_name: String::from("p1"),
            arguments: vec![
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v2"),
                        typ: polymorphic::Type::Bool,
                    },
                    position: position.clone(),
                }),
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v3"),
                        typ: polymorphic::Type::Int,
                    },
                    position: position.clone(),
                }),
            ],
            permission: polymorphic::PermAmount::Write,
            enum_variant: Some(polymorphic::EnumVariantIndex::new(String::from("evi"))),
            position: position.clone(),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // Unfold
        source = polymorphic::Stmt::Unfold(polymorphic::Unfold {
            predicate_name: String::from("p1"),
            arguments: vec![
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v2"),
                        typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                            label: String::from("E"),
                        }),
                    },
                    position: position.clone(),
                }),
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v3"),
                        typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                            label: String::from("T"),
                        }),
                    },
                    position: position.clone(),
                }),
            ],
            permission: polymorphic::PermAmount::Write,
            enum_variant: Some(polymorphic::EnumVariantIndex::new(String::from("evi"))),
        });
        expected = polymorphic::Stmt::Unfold(polymorphic::Unfold {
            predicate_name: String::from("p1"),
            arguments: vec![
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v2"),
                        typ: polymorphic::Type::Bool,
                    },
                    position: position.clone(),
                }),
                polymorphic::Expr::Local(polymorphic::Local {
                    variable: polymorphic::LocalVar {
                        name: String::from("_v3"),
                        typ: polymorphic::Type::Int,
                    },
                    position: position.clone(),
                }),
            ],
            permission: polymorphic::PermAmount::Write,
            enum_variant: Some(polymorphic::EnumVariantIndex::new(String::from("evi"))),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // Obtain
        source = polymorphic::Stmt::Obtain(polymorphic::Obtain {
            predicate_name: polymorphic::Expr::Local(polymorphic::Local {
                variable: polymorphic::LocalVar {
                    name: String::from("_v1"),
                    typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                        label: String::from("T"),
                    }),
                },
                position: position.clone(),
            }),
            position: position.clone(),
        });
        expected = polymorphic::Stmt::Obtain(polymorphic::Obtain {
            predicate_name: polymorphic::Expr::Local(polymorphic::Local {
                variable: polymorphic::LocalVar {
                    name: String::from("_v1"),
                    typ: polymorphic::Type::Int,
                },
                position: position.clone(),
            }),
            position: position.clone(),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // BeinFrame
        source = polymorphic::Stmt::BeginFrame(polymorphic::BeginFrame {});
        expected = polymorphic::Stmt::BeginFrame(polymorphic::BeginFrame {});
        test(source, expected, &SUBSTITUTION_MAP);

        // EndFrame
        source = polymorphic::Stmt::EndFrame(polymorphic::EndFrame {});
        expected = polymorphic::Stmt::EndFrame(polymorphic::EndFrame {});
        test(source, expected, &SUBSTITUTION_MAP);

        // TransferPerm
        source = polymorphic::Stmt::TransferPerm(polymorphic::TransferPerm {
            left: polymorphic::Expr::Local(polymorphic::Local {
                variable: polymorphic::LocalVar {
                    name: String::from("_v1"),
                    typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                        label: String::from("T"),
                    }),
                },
                position: position.clone(),
            }),
            right: polymorphic::Expr::Local(polymorphic::Local {
                variable: polymorphic::LocalVar {
                    name: String::from("_v2"),
                    typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                        label: String::from("E"),
                    }),
                },
                position: position.clone(),
            }),
            unchecked: true,
        });
        expected = polymorphic::Stmt::TransferPerm(polymorphic::TransferPerm {
            left: polymorphic::Expr::Local(polymorphic::Local {
                variable: polymorphic::LocalVar {
                    name: String::from("_v1"),
                    typ: polymorphic::Type::Int,
                },
                position: position.clone(),
            }),
            right: polymorphic::Expr::Local(polymorphic::Local {
                variable: polymorphic::LocalVar {
                    name: String::from("_v2"),
                    typ: polymorphic::Type::Bool,
                },
                position: position.clone(),
            }),
            unchecked: true,
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // PackageMagicWand
        source = polymorphic::Stmt::PackageMagicWand(polymorphic::PackageMagicWand {
            magic_wand: polymorphic::Expr::Local(polymorphic::Local {
                variable: polymorphic::LocalVar {
                    name: String::from("_v1"),
                    typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                        label: String::from("T"),
                    }),
                },
                position: position.clone(),
            }),
            package_stmts: vec![
                polymorphic::Stmt::Inhale(polymorphic::Inhale {
                    expr: polymorphic::Expr::Local(polymorphic::Local {
                        variable: polymorphic::LocalVar {
                            name: String::from("_v2"),
                            typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                                label: String::from("T"),
                            }),
                        },
                        position: position.clone(),
                    }),
                }),
                polymorphic::Stmt::Exhale(polymorphic::Exhale {
                    expr: polymorphic::Expr::Local(polymorphic::Local {
                        variable: polymorphic::LocalVar {
                            name: String::from("_v3"),
                            typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                                label: String::from("E"),
                            }),
                        },
                        position: position.clone(),
                    }),
                    position: position.clone(),
                })
            ],
            label: String::from("l1"),
            variables: vec![
                polymorphic::LocalVar {
                    name: String::from("_v4"),
                    typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                        label: String::from("T"),
                    }),
                },
                polymorphic::LocalVar {
                    name: String::from("_v5"),
                    typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                        label: String::from("E"),
                    }),
                },
            ],
            position: position.clone(),
        });
        expected = polymorphic::Stmt::PackageMagicWand(polymorphic::PackageMagicWand {
            magic_wand: polymorphic::Expr::Local(polymorphic::Local {
                variable: polymorphic::LocalVar {
                    name: String::from("_v1"),
                    typ: polymorphic::Type::Int,
                },
                position: position.clone(),
            }),
            package_stmts: vec![
                polymorphic::Stmt::Inhale(polymorphic::Inhale {
                    expr: polymorphic::Expr::Local(polymorphic::Local {
                        variable: polymorphic::LocalVar {
                            name: String::from("_v2"),
                            typ: polymorphic::Type::Int,
                        },
                        position: position.clone(),
                    }),
                }),
                polymorphic::Stmt::Exhale(polymorphic::Exhale {
                    expr: polymorphic::Expr::Local(polymorphic::Local {
                        variable: polymorphic::LocalVar {
                            name: String::from("_v3"),
                            typ: polymorphic::Type::Bool,
                        },
                        position: position.clone(),
                    }),
                    position: position.clone(),
                })
            ],
            label: String::from("l1"),
            variables: vec![
                polymorphic::LocalVar {
                    name: String::from("_v4"),
                    typ: polymorphic::Type::Int,
                },
                polymorphic::LocalVar {
                    name: String::from("_v5"),
                    typ: polymorphic::Type::Bool,
                },
            ],
            position: position.clone(),
        });
        test(source, expected, &SUBSTITUTION_MAP);

       // ApplyMagicWand
        source = polymorphic::Stmt::ApplyMagicWand(polymorphic::ApplyMagicWand {
            magic_wand: polymorphic::Expr::Local(polymorphic::Local {
                variable: polymorphic::LocalVar {
                    name: String::from("_v1"),
                    typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                        label: String::from("T"),
                    }),
                },
                position: position.clone(),
            }),
            position: position.clone(),
        });
        expected = polymorphic::Stmt::ApplyMagicWand(polymorphic::ApplyMagicWand {
            magic_wand: polymorphic::Expr::Local(polymorphic::Local {
                variable: polymorphic::LocalVar {
                    name: String::from("_v1"),
                    typ: polymorphic::Type::Int,
                },
                position: position.clone(),
            }),
            position: position.clone(),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // ExpireBorrows TODO: add this after DAG is checked

        // If
        source = polymorphic::Stmt::If(polymorphic::If {
            guard: polymorphic::Expr::Local(polymorphic::Local {
                variable: polymorphic::LocalVar {
                    name: String::from("_v1"),
                    typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                        label: String::from("T"),
                    }),
                },
                position: position.clone(),
            }),
            then_stmts: vec![
                polymorphic::Stmt::Inhale(polymorphic::Inhale {
                    expr: polymorphic::Expr::Local(polymorphic::Local {
                        variable: polymorphic::LocalVar {
                            name: String::from("_v2"),
                            typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                                label: String::from("T"),
                            }),
                        },
                        position: position.clone(),
                    }),
                }),
                polymorphic::Stmt::Exhale(polymorphic::Exhale {
                    expr: polymorphic::Expr::Local(polymorphic::Local {
                        variable: polymorphic::LocalVar {
                            name: String::from("_v3"),
                            typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                                label: String::from("E"),
                            }),
                        },
                        position: position.clone(),
                    }),
                    position: position.clone(),
                })
            ],
            else_stmts: vec![
                polymorphic::Stmt::Inhale(polymorphic::Inhale {
                    expr: polymorphic::Expr::Local(polymorphic::Local {
                        variable: polymorphic::LocalVar {
                            name: String::from("_v4"),
                            typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                                label: String::from("T"),
                            }),
                        },
                        position: position.clone(),
                    }),
                }),
                polymorphic::Stmt::Exhale(polymorphic::Exhale {
                    expr: polymorphic::Expr::Local(polymorphic::Local {
                        variable: polymorphic::LocalVar {
                            name: String::from("_v5"),
                            typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                                label: String::from("E"),
                            }),
                        },
                        position: position.clone(),
                    }),
                    position: position.clone(),
                })
            ],
        });
        expected = polymorphic::Stmt::If(polymorphic::If {
            guard: polymorphic::Expr::Local(polymorphic::Local {
                variable: polymorphic::LocalVar {
                    name: String::from("_v1"),
                    typ: polymorphic::Type::Int,
                },
                position: position.clone(),
            }),
            then_stmts: vec![
                polymorphic::Stmt::Inhale(polymorphic::Inhale {
                    expr: polymorphic::Expr::Local(polymorphic::Local {
                        variable: polymorphic::LocalVar {
                            name: String::from("_v2"),
                            typ: polymorphic::Type::Int,
                        },
                        position: position.clone(),
                    }),
                }),
                polymorphic::Stmt::Exhale(polymorphic::Exhale {
                    expr: polymorphic::Expr::Local(polymorphic::Local {
                        variable: polymorphic::LocalVar {
                            name: String::from("_v3"),
                            typ: polymorphic::Type::Bool,
                        },
                        position: position.clone(),
                    }),
                    position: position.clone(),
                })
            ],
            else_stmts: vec![
                polymorphic::Stmt::Inhale(polymorphic::Inhale {
                    expr: polymorphic::Expr::Local(polymorphic::Local {
                        variable: polymorphic::LocalVar {
                            name: String::from("_v4"),
                            typ: polymorphic::Type::Int,
                        },
                        position: position.clone(),
                    }),
                }),
                polymorphic::Stmt::Exhale(polymorphic::Exhale {
                    expr: polymorphic::Expr::Local(polymorphic::Local {
                        variable: polymorphic::LocalVar {
                            name: String::from("_v5"),
                            typ: polymorphic::Type::Bool,
                        },
                        position: position.clone(),
                    }),
                    position: position.clone(),
                })
            ],
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // Downcast
        source = polymorphic::Stmt::Downcast(polymorphic::Downcast {
            base: polymorphic::Expr::Local(polymorphic::Local {
                variable: polymorphic::LocalVar {
                    name: String::from("_v1"),
                    typ: polymorphic::Type::Int,
                },
                position: position.clone(),
            }),
            field: polymorphic::Field {
                name: String::from("f1"),
                typ: polymorphic::Type::Bool,
            }
        });
        expected = polymorphic::Stmt::Downcast(polymorphic::Downcast {
            base: polymorphic::Expr::Local(polymorphic::Local {
                variable: polymorphic::LocalVar {
                    name: String::from("_v1"),
                    typ: polymorphic::Type::Int,
                },
                position: position.clone(),
            }),
            field: polymorphic::Field {
                name: String::from("f1"),
                typ: polymorphic::Type::Bool,
            }
        });
        test(source, expected, &SUBSTITUTION_MAP);
    }

    #[test]
    // successful substitution within BodylessMethod
    fn substitution_type_var_bodyless_method_test() {
        let source = polymorphic::BodylessMethod {
            name: String::from("bm1"),
            formal_args: vec![
                polymorphic::LocalVar {
                    name: String::from("_v1"),
                    typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                        label: String::from("T"),
                    }),
                },
                polymorphic::LocalVar {
                    name: String::from("_v2"),
                    typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                        label: String::from("D"),
                    }),
                },
            ],
            formal_returns: vec![
                polymorphic::LocalVar {
                    name: String::from("_r"),
                    typ: polymorphic::Type::TypedRef(polymorphic::TypedRef {
                        label: String::from("CustomStruct"),
                        arguments: vec![
                            polymorphic::Type::TypeVar(polymorphic::TypeVar {
                                label: String::from("E"),
                            }),
                            polymorphic::Type::TypeVar(polymorphic::TypeVar {
                                label: String::from("F"),
                            }),
                        ],
                    }),
                }
            ],
        };

        let expected = polymorphic::BodylessMethod {
            name: String::from("bm1"),
            formal_args: vec![
                polymorphic::LocalVar {
                    name: String::from("_v1"),
                    typ: polymorphic::Type::Int,
                },
                polymorphic::LocalVar {
                    name: String::from("_v2"),
                    typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                        label: String::from("D"),
                    }),
                },
            ],
            formal_returns: vec![
                polymorphic::LocalVar {
                    name: String::from("_r"),
                    typ: polymorphic::Type::TypedRef(polymorphic::TypedRef {
                        label: String::from("CustomStruct"),
                        arguments: vec![
                            polymorphic::Type::Bool,
                            polymorphic::Type::TypedRef(polymorphic::TypedRef {
                                label: String::from("SimpleRef"),
                                arguments: vec![],
                            })
                        ],
                    })
                },
            ],
        };
        test(source, expected, &SUBSTITUTION_MAP);
    }

    #[test]
    // successful substitution within DomainFunc
    fn substitution_type_var_domain_func_test() {
        let source = polymorphic::DomainFunc {
            name: String::from("df"),
            formal_args: vec![
                polymorphic::LocalVar {
                    name: String::from("_v1"),
                    typ: polymorphic::Type::Int,
                },
                polymorphic::LocalVar {
                    name: String::from("_v2"),
                    typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                        label: String::from("D"),
                    }),
                },
            ],
            return_type: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                label: String::from("T"),
            }),
            unique: true,
            domain_name: String::from("dn"),
        };

        let expected = polymorphic::DomainFunc {
            name: String::from("df"),
            formal_args: vec![
                polymorphic::LocalVar {
                    name: String::from("_v1"),
                    typ: polymorphic::Type::Int,
                },
                polymorphic::LocalVar {
                    name: String::from("_v2"),
                    typ: polymorphic::Type::TypeVar(polymorphic::TypeVar {
                        label: String::from("D"),
                    }),
                },
            ],
            return_type: polymorphic::Type::Int,
            unique: true,
            domain_name: String::from("dn"),
        };
        test(source, expected, &SUBSTITUTION_MAP);
    }
}
