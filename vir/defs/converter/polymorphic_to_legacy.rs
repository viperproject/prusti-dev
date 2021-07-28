use std::{ 
    fmt,
    collections::HashMap,
};

use super::super::polymorphic::*;
use uuid::Uuid;

pub trait Generic {
    fn substitute(self, map: &HashMap<TypeVar, Type>) -> Self;
}

#[cfg(test)]
mod tests {
    use super::*;

    lazy_static! {
        static ref SUBSTITUTION_MAP : HashMap<TypeVar, Type> = {
            let mut m = HashMap::new();
            m.insert(TypeVar { label: String::from("T") }, Type::Int);
            m.insert(TypeVar { label: String::from("E") }, Type::Bool);
            m.insert(TypeVar { label: String::from("F") }, Type::TypedRef(TypedRef {
                label: String::from("SimpleRef"),
                arguments: vec![],
            }));
            // Substitution into other type vars that have a mapping
            m.insert(TypeVar { label: String::from("G") }, Type::TypedRef(TypedRef {
                label: String::from("ComplexRef"),
                arguments: vec![Type::TypeVar(TypeVar {label: String::from("T") })],
            }));
            // Subsitutition into the same type vars used for substitution
            m.insert(TypeVar { label: String::from("H") }, Type::TypedRef(TypedRef {
                label: String::from("ComplexRef2"),
                arguments: vec![
                    Type::TypeVar(TypeVar {label: String::from("H") }), 
                    Type::Domain(DomainType {
                        label: String::from("ComplexDomain"), 
                        arguments: vec![Type::TypeVar(TypeVar {label: String::from("T")})],
                    })
                ],
            }));
            m
        };
    }

    // Compare the results after substitution with expected value
    fn test<T>(source: T, expected: T, map: &HashMap<TypeVar, Type>) where T: Generic, T: fmt::Debug, T: PartialEq {
        let substituted = source.substitute(map);
        assert_eq!(substituted, expected);
    }

    #[test]
    // source having no type var for substitution
    fn substitution_no_type_var_test() {
        let mut source = Type::Int;
        let mut expected = source.clone();
        test(source, expected, &SUBSTITUTION_MAP);

        source = Type::Bool;
        expected = source.clone();
        test(source, expected, &SUBSTITUTION_MAP);

        source = Type::TypedRef(TypedRef {
            label: String::from("CustomStruct"),
            arguments: vec![Type::Int],
        });
        expected = source.clone();
        test(source, expected, &SUBSTITUTION_MAP);

        source = Type::Domain(DomainType {
            label: String::from("CustomDomain"),
            arguments: vec![],
        });
        expected = source.clone();
        test(source, expected, &SUBSTITUTION_MAP);

        source = Type::Snapshot(SnapshotType {
            label: String::from("CustomSnapshot"),
            arguments: vec![
                Type::Bool, 
                Type::TypedRef(
                    TypedRef {
                        label: String::from("vec"),
                        arguments: vec![Type::Bool],
                    }
                )
            ],
        });
        expected = source.clone();
        test(source, expected, &SUBSTITUTION_MAP);

        source = Type::TypeVar(TypeVar {
            label: String::from("CustomTypeVar"),
        });
        expected = source.clone();
        test(source, expected, &SUBSTITUTION_MAP);
    }

    #[test]
    // source having no matching type var for substitution
    fn substitution_no_matching_type_var_test() {
        let mut source = Type::TypedRef(TypedRef {
            label: String::from("CustomStruct"),
            arguments: vec![Type::TypeVar(TypeVar {
                label: String::from("D"),
            })],
        });
        let mut expected = source.clone();
        test(source, expected, &SUBSTITUTION_MAP);

        source = Type::Domain(DomainType {
            label: String::from("CustomDomain"),
            arguments: vec![
                Type::TypeVar(TypeVar {
                    label: String::from("C"),
                }),
                Type::Int,
                Type::TypeVar(TypeVar {
                    label: String::from("D"),
                }),
            ],
        });
        expected = source.clone();
        test(source, expected, &SUBSTITUTION_MAP);

        source = Type::Snapshot(SnapshotType {
            label: String::from("Custom"),
            arguments: vec![
                Type::Bool,
                Type::TypedRef(
                    TypedRef {
                        label: String::from("vec"),
                        arguments: vec![Type::TypeVar(TypeVar {
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
        let mut source = Type::TypeVar(TypeVar {
            label: String::from("T"),
        });
        let mut expected = Type::Int;
        test(source, expected, &SUBSTITUTION_MAP);

        source = Type::TypedRef(TypedRef {
            label: String::from("CustomStruct"),
            arguments: vec![
                Type::TypeVar(TypeVar {
                    label: String::from("E"),
                }),
                Type::TypeVar(TypeVar {
                    label: String::from("F"),
                }),
            ],
        });
        expected = Type::TypedRef(TypedRef {
            label: String::from("CustomStruct"),
            arguments: vec![
                Type::Bool,
                Type::TypedRef(TypedRef {
                    label: String::from("SimpleRef"),
                    arguments: vec![],
                })
            ],
        });
        test(source, expected, &SUBSTITUTION_MAP);

        source = Type::Domain(DomainType {
            label: String::from("CustomDomain"),
            arguments: vec![
                Type::TypeVar(TypeVar {
                    label: String::from("E"),
                }),
                Type::TypeVar(TypeVar {
                    label: String::from("F"),
                }),
            ],
        });
        expected = Type::Domain(DomainType {
            label: String::from("CustomDomain"),
            arguments: vec![
                Type::Bool,
                Type::TypedRef(TypedRef {
                    label: String::from("SimpleRef"),
                    arguments: vec![],
                })
            ],
        });
        test(source, expected, &SUBSTITUTION_MAP);

        source = Type::Snapshot(SnapshotType {
            label: String::from("CustomSnapshot"),
            arguments: vec![
                Type::TypeVar(TypeVar {
                    label: String::from("E"),
                }),
                Type::TypeVar(TypeVar {
                    label: String::from("F"),
                }),
            ],
        });
        expected = Type::Snapshot(SnapshotType {
            label: String::from("CustomSnapshot"),
            arguments: vec![
                Type::Bool,
                Type::TypedRef(TypedRef {
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
        let mut source = Type::TypedRef(TypedRef {
            label: String::from("CustomStruct"),
            arguments: vec![
                Type::Int,
                Type::Domain(DomainType {
                    label: String::from("CustomDomain"),
                    arguments: vec![
                        Type::TypeVar(TypeVar {
                            label: String::from("E"),
                        }),
                        Type::Snapshot(SnapshotType {
                            label: String::from("CustomSnapshot"),
                            arguments: vec![
                                Type::TypeVar(TypeVar {
                                    label: String::from("F"),
                                }),
                            ]    
                        }),
                    ]
                }),
            ],
        });
        let mut expected = Type::TypedRef(TypedRef {
            label: String::from("CustomStruct"),
            arguments: vec![
                Type::Int,
                Type::Domain(DomainType {
                    label: String::from("CustomDomain"),
                    arguments: vec![
                        Type::Bool,
                        Type::Snapshot(SnapshotType {
                            label: String::from("CustomSnapshot"),
                            arguments: vec![
                                Type::TypedRef(TypedRef {
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
        let mut source = Type::TypedRef(TypedRef {
            label: String::from("CustomStruct"),
            arguments: vec![
                Type::TypeVar(TypeVar {
                    label: String::from("G"),
                }),
                Type::Domain(DomainType {
                    label: String::from("CustomDomain"),
                    arguments: vec![
                        Type::TypeVar(TypeVar {
                            label: String::from("H"),
                        }),
                        Type::Snapshot(SnapshotType {
                            label: String::from("CustomSnapshot"),
                            arguments: vec![
                                Type::TypeVar(TypeVar {
                                    label: String::from("F"),
                                }),
                            ]    
                        }),
                    ]
                }),
            ],
        });
        let mut expected = Type::TypedRef(TypedRef {
            label: String::from("CustomStruct"),
            arguments: vec![
                Type::TypedRef(TypedRef {
                    label: String::from("ComplexRef"),
                    arguments: vec![Type::TypeVar(TypeVar {label: String::from("T") })],
                }),
                Type::Domain(DomainType {
                    label: String::from("CustomDomain"),
                    arguments: vec![
                        Type::TypedRef(TypedRef {
                            label: String::from("ComplexRef2"),
                            arguments: vec![
                                Type::TypeVar(TypeVar {label: String::from("H") }), 
                                Type::Domain(DomainType {
                                    label: String::from("ComplexDomain"), 
                                    arguments: vec![Type::TypeVar(TypeVar {label: String::from("T")})],
                                })
                            ],
                        }),
                        Type::Snapshot(SnapshotType {
                            label: String::from("CustomSnapshot"),
                            arguments: vec![
                                Type::TypedRef(TypedRef {
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
        let source = LocalVar {
            name: String::from("_v1"),
            typ: Type::TypeVar(TypeVar {
                label: String::from("T"),
            }),
        };
        let expected = LocalVar {
            name: String::from("_v1"),
            typ: Type::Int,
        };
        test(source, expected, &SUBSTITUTION_MAP);
    }

    #[test]
    // successful substitution within Field
    fn substitution_type_var_field_test() {
        let source = Field {
            name: String::from("_f1"),
            typ: Type::TypeVar(TypeVar {
                label: String::from("T"),
            }),
        };
        let expected = Field {
            name: String::from("_f1"),
            typ: Type::Int,
        };
        test(source, expected, &SUBSTITUTION_MAP);
    }

    #[test]
    // successful substitution within Expr, going over all variants
    fn substitution_type_var_expr_test() {
        // dummy position for convenient copying
        let position = Position::new(1, 2, 3);

        // Local
        let mut source = Expr::Local(Local {
            variable: LocalVar {
                name: String::from("_v1"),
                typ: Type::TypeVar(TypeVar {
                    label: String::from("T"),
                }),
            },
            position: position.clone(),
        });
        let mut expected = Expr::Local(Local {
            variable: LocalVar {
                name: String::from("_v1"),
                typ: Type::Int,
            },
            position: position.clone(),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // Variant
        source = Expr::Variant(Variant {
            base: Box::new(
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v1"),
                        typ: Type::TypeVar(TypeVar {
                            label: String::from("T"),
                        }),
                    },
                    position: position.clone(),
            })),
            variant_index: Field {
                name: String::from("_f1"),
                typ: Type::TypeVar(TypeVar {
                    label: String::from("T"),
                }),
            },
            position: position.clone(),
        });
        expected = Expr::Variant(Variant {
            base: Box::new(
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v1"),
                        typ: Type::Int,
                    },
                    position: position.clone(),
            })),
            variant_index: Field {
                name: String::from("_f1"),
                typ: Type::Int,
            },
            position: position.clone(),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // Field
        source = Expr::Field(FieldExpr {
            base: Box::new(
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v1"),
                        typ: Type::TypeVar(TypeVar {
                            label: String::from("T"),
                        }),
                    },
                    position: position.clone(),
            })),
            field: Field {
                name: String::from("_f1"),
                typ: Type::TypeVar(TypeVar {
                    label: String::from("T"),
                }),
            },
            position: position.clone(),
        });
        expected = Expr::Field(FieldExpr {
            base: Box::new(
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v1"),
                        typ: Type::Int,
                    },
                    position: position.clone(),
            })),
            field: Field {
                name: String::from("_f1"),
                typ: Type::Int,
            },
            position: position.clone(),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // AddrOf
        source = Expr::AddrOf(AddrOf {
            base: Box::new(
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v1"),
                        typ: Type::TypeVar(TypeVar {
                            label: String::from("T"),
                        }),
                    },
                    position: position.clone(),
            })),
            addr_type: Type::TypeVar(TypeVar {
                label: String::from("E"),
            }),
            position: position.clone(),
        });
        expected = Expr::AddrOf(AddrOf {
            base: Box::new(
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v1"),
                        typ: Type::Int,
                    },
                    position: position.clone(),
            })),
            addr_type: Type::Bool,
            position: position.clone(),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // LabelledOld
        source = Expr::LabelledOld(LabelledOld {
            label: String::from("l1"),
            base: Box::new(
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v1"),
                        typ: Type::TypeVar(TypeVar {
                            label: String::from("T"),
                        }),
                    },
                    position: position.clone(),
            })),
            position: position.clone(),
        });
        expected = Expr::LabelledOld(LabelledOld {
            label: String::from("l1"),
            base: Box::new(
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v1"),
                        typ: Type::Int,
                    },
                    position: position.clone(),
            })),
            position: position.clone(),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // Const
        source = Expr::Const(ConstExpr {
            value: Const::Int(123),
            position: position.clone(),
        });
        expected = Expr::Const(ConstExpr {
            value: Const::Int(123),
            position: position.clone(),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // MagicWand
        source = Expr::MagicWand(MagicWand {
            left: Box::new(
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_left"),
                        typ: Type::TypeVar(TypeVar {
                            label: String::from("T"),
                        }),
                    },
                    position: position.clone(),
            })),
            right: Box::new(
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_right"),
                        typ: Type::TypeVar(TypeVar {
                            label: String::from("E"),
                        }),
                    },
                    position: position.clone(),
            })),
            borrow: Some(Borrow(123)),
            position: position.clone(),
        });
        expected = Expr::MagicWand(MagicWand {
            left: Box::new(
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_left"),
                        typ: Type::Int,
                    },
                    position: position.clone(),
            })),
            right: Box::new(
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_right"),
                        typ: Type::Bool,
                    },
                    position: position.clone(),
            })),
            borrow: Some(Borrow(123)),
            position: position.clone(),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // PredicateAccessPredicate
        source = Expr::PredicateAccessPredicate(PredicateAccessPredicate {
            predicate_name: String::from("_p1"),
            argument: Box::new(
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v1"),
                        typ: Type::TypeVar(TypeVar {
                            label: String::from("T"),
                        }),
                    },
                    position: position.clone(),
            })),
            permission: PermAmount::Read,
            position: position.clone(),
        });
        expected = Expr::PredicateAccessPredicate(PredicateAccessPredicate {
            predicate_name: String::from("_p1"),
            argument: Box::new(
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v1"),
                        typ: Type::Int,
                    },
                    position: position.clone(),
            })),
            permission: PermAmount::Read,
            position: position.clone(),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // FieldAccessPredicate
        source = Expr::FieldAccessPredicate(FieldAccessPredicate {
            base: Box::new(
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v1"),
                        typ: Type::TypeVar(TypeVar {
                            label: String::from("T"),
                        }),
                    },
                    position: position.clone(),
            })),
            permission: PermAmount::Read,
            position: position.clone(),
        });
        expected = Expr::FieldAccessPredicate(FieldAccessPredicate {
            base: Box::new(
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v1"),
                        typ: Type::Int,
                    },
                    position: position.clone(),
            })),
            permission: PermAmount::Read,
            position: position.clone(),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // UnaryOp
        source = Expr::UnaryOp(UnaryOp {
            op_kind: UnaryOpKind::Minus,
            argument: Box::new(
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v1"),
                        typ: Type::TypeVar(TypeVar {
                            label: String::from("T"),
                        }),
                    },
                    position: position.clone(),
            })),
            position: position.clone(),
        });
        expected = Expr::UnaryOp(UnaryOp {
            op_kind: UnaryOpKind::Minus,
            argument: Box::new(
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v1"),
                        typ: Type::Int,
                    },
                    position: position.clone(),
            })),
            position: position.clone(),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // BinOp
        source = Expr::BinOp(BinOp {
            op_kind: BinOpKind::Mul,
            left: Box::new(
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v1"),
                        typ: Type::TypeVar(TypeVar {
                            label: String::from("T"),
                        }),
                    },
                    position: position.clone(),
            })),
            right: Box::new(
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v2"),
                        typ: Type::TypeVar(TypeVar {
                            label: String::from("E"),
                        }),
                    },
                    position: position.clone(),
            })),
            position: position.clone(),
        });
        expected = Expr::BinOp(BinOp {
            op_kind: BinOpKind::Mul,
            left: Box::new(
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v1"),
                        typ: Type::Int,
                    },
                    position: position.clone(),
            })),
            right: Box::new(
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v2"),
                        typ: Type::Bool,
                    },
                    position: position.clone(),
            })),
            position: position.clone(),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // ContainerOp
        source = Expr::ContainerOp(ContainerOp {
            op_kind: ContainerOpKind::SeqConcat,
            left: Box::new(
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v1"),
                        typ: Type::TypeVar(TypeVar {
                            label: String::from("T"),
                        }),
                    },
                    position: position.clone(),
            })),
            right: Box::new(
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v2"),
                        typ: Type::TypeVar(TypeVar {
                            label: String::from("E"),
                        }),
                    },
                    position: position.clone(),
            })),
            position: position.clone(),
        });
        expected = Expr::ContainerOp(ContainerOp {
            op_kind: ContainerOpKind::SeqConcat,
            left: Box::new(
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v1"),
                        typ: Type::Int,
                    },
                    position: position.clone(),
            })),
            right: Box::new(
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v2"),
                        typ: Type::Bool,
                    },
                    position: position.clone(),
            })),
            position: position.clone(),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // Seq
        source = Expr::Seq(Seq {
            typ: Type::TypeVar(TypeVar {
                label: String::from("T"),
            }),
            elements: vec![
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v1"),
                        typ: Type::TypeVar(TypeVar {
                            label: String::from("T"),
                        }),
                    },
                    position: position.clone(),
                }),
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v2"),
                        typ: Type::TypeVar(TypeVar {
                            label: String::from("E"),
                        }),
                    },
                    position: position.clone(),
                }),
            ],
            position: position.clone(),
        });
        expected = Expr::Seq(Seq {
            typ: Type::Int,
            elements: vec![
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v1"),
                        typ: Type::Int,
                    },
                    position: position.clone(),
                }),
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v2"),
                        typ: Type::Bool,
                    },
                    position: position.clone(),
                }),
            ],
            position: position.clone(),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // Unfolding
        source = Expr::Unfolding(Unfolding {
            predicate_name: String::from("p1"),
            arguments: vec![
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v1"),
                        typ: Type::TypeVar(TypeVar {
                            label: String::from("T"),
                        }),
                    },
                    position: position.clone(),
                }),
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v2"),
                        typ: Type::TypeVar(TypeVar {
                            label: String::from("E"),
                        }),
                    },
                    position: position.clone(),
                }),
            ],
            base: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v3"),
                    typ: Type::TypeVar(TypeVar {
                        label: String::from("T"),
                    }),
                },
                position: position.clone(),
            })),
            permission: PermAmount::Write,
            variant: Some(EnumVariantIndex::new(String::from("evi"))),
            position: position.clone(),
        });
        expected = Expr::Unfolding(Unfolding {
            predicate_name: String::from("p1"),
            arguments: vec![
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v1"),
                        typ: Type::Int,
                    },
                    position: position.clone(),
                }),
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v2"),
                        typ: Type::Bool,
                    },
                    position: position.clone(),
                }),
            ],
            base: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v3"),
                    typ: Type::Int,
                },
                position: position.clone(),
            })),
            permission: PermAmount::Write,
            variant: Some(EnumVariantIndex::new(String::from("evi"))),
            position: position.clone(),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // Cond
        source = Expr::Cond(Cond {
            guard: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::TypeVar(TypeVar {
                        label: String::from("T"),
                    }),
                },
                position: position.clone(),
            })),
            then_expr: Box::new( Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v2"),
                    typ: Type::TypeVar(TypeVar {
                        label: String::from("E"),
                    }),
                },
                position: position.clone(),
            })),
            else_expr: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v3"),
                    typ: Type::TypeVar(TypeVar {
                        label: String::from("T"),
                    }),
                },
                position: position.clone(),
            })),
            position: position.clone(),
        });
        expected = Expr::Cond(Cond {
            guard: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::Int,
                },
                position: position.clone(),
            })),
            then_expr: Box::new( Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v2"),
                    typ: Type::Bool,
                },
                position: position.clone(),
            })),
            else_expr: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v3"),
                    typ: Type::Int,
                },
                position: position.clone(),
            })),
            position: position.clone(),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // ForAll
        source = Expr::ForAll(ForAll {
            variables: vec![
                LocalVar {
                    name: String::from("_v1"),
                    typ: Type::TypeVar(TypeVar {
                        label: String::from("T"),
                    }),
                },
                LocalVar {
                    name: String::from("_v2"),
                    typ: Type::TypeVar(TypeVar {
                        label: String::from("E"),
                    }),
                },
            ],
            triggers: vec![
                Trigger::new(
                    vec![
                        Expr::Local(Local {
                            variable: LocalVar {
                                name: String::from("_v3"),
                                typ: Type::TypeVar(TypeVar {
                                    label: String::from("T"),
                                }),
                            },
                            position: position.clone(),
                        }),
                        Expr::Local(Local {
                            variable: LocalVar {
                                name: String::from("_v4"),
                                typ: Type::TypeVar(TypeVar {
                                    label: String::from("E"),
                                }),
                            },
                            position: position.clone(),
                        })
                    ]
                )
            ],
            body: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v5"),
                    typ: Type::TypeVar(TypeVar {
                        label: String::from("T"),
                    }),
                },
                position: position.clone(),
            })),
            position: position.clone(),
        });
        expected = Expr::ForAll(ForAll {
            variables: vec![
                LocalVar {
                    name: String::from("_v1"),
                    typ: Type::Int,
                },
                LocalVar {
                    name: String::from("_v2"),
                    typ: Type::Bool,
                },
            ],
            triggers: vec![
                Trigger::new(
                    vec![
                        Expr::Local(Local {
                            variable: LocalVar {
                                name: String::from("_v3"),
                                typ: Type::Int,
                            },
                            position: position.clone(),
                        }),
                        Expr::Local(Local {
                            variable: LocalVar {
                                name: String::from("_v4"),
                                typ: Type::Bool,
                            },
                            position: position.clone(),
                        })
                    ]
                )
            ],
            body: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v5"),
                    typ: Type::Int,
                },
                position: position.clone(),
            })),
            position: position.clone(),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // Exists
        source = Expr::Exists(Exists {
            variables: vec![
                LocalVar {
                    name: String::from("_v1"),
                    typ: Type::TypeVar(TypeVar {
                        label: String::from("T"),
                    }),
                },
                LocalVar {
                    name: String::from("_v2"),
                    typ: Type::TypeVar(TypeVar {
                        label: String::from("E"),
                    }),
                },
            ],
            triggers: vec![
                Trigger::new(
                    vec![
                        Expr::Local(Local {
                            variable: LocalVar {
                                name: String::from("_v3"),
                                typ: Type::TypeVar(TypeVar {
                                    label: String::from("T"),
                                }),
                            },
                            position: position.clone(),
                        }),
                        Expr::Local(Local {
                            variable: LocalVar {
                                name: String::from("_v4"),
                                typ: Type::TypeVar(TypeVar {
                                    label: String::from("E"),
                                }),
                            },
                            position: position.clone(),
                        })
                    ]
                )
            ],
            body: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v5"),
                    typ: Type::TypeVar(TypeVar {
                        label: String::from("T"),
                    }),
                },
                position: position.clone(),
            })),
            position: position.clone(),
        });
        expected = Expr::Exists(Exists {
            variables: vec![
                LocalVar {
                    name: String::from("_v1"),
                    typ: Type::Int,
                },
                LocalVar {
                    name: String::from("_v2"),
                    typ: Type::Bool,
                },
            ],
            triggers: vec![
                Trigger::new(
                    vec![
                        Expr::Local(Local {
                            variable: LocalVar {
                                name: String::from("_v3"),
                                typ: Type::Int,
                            },
                            position: position.clone(),
                        }),
                        Expr::Local(Local {
                            variable: LocalVar {
                                name: String::from("_v4"),
                                typ: Type::Bool,
                            },
                            position: position.clone(),
                        })
                    ]
                )
            ],
            body: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v5"),
                    typ: Type::Int,
                },
                position: position.clone(),
            })),
            position: position.clone(),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // LetExpr
        source = Expr::LetExpr(LetExpr {
            variable: LocalVar {
                name: String::from("_v1"),
                typ: Type::TypeVar(TypeVar {
                    label: String::from("T"),
                }),
            },
            def:Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v2"),
                    typ: Type::TypeVar(TypeVar {
                        label: String::from("E"),
                    }),
                },
                position: position.clone(),
            })),
            body: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v3"),
                    typ: Type::TypeVar(TypeVar {
                        label: String::from("T"),
                    }),
                },
                position: position.clone(),
            })),
            position: position.clone(),
        });
        expected = Expr::LetExpr(LetExpr {
            variable: LocalVar {
                name: String::from("_v1"),
                typ: Type::Int,
            },
            def:Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v2"),
                    typ: Type::Bool,
                },
                position: position.clone(),
            })),
            body: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v3"),
                    typ: Type::Int,
                },
                position: position.clone(),
            })),
            position: position.clone(),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // FuncApp
        source = Expr::FuncApp(FuncApp {
            function_name: String::from("f1"),
            arguments: vec![
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v2"),
                        typ: Type::TypeVar(TypeVar {
                            label: String::from("E"),
                        }),
                    },
                    position: position.clone(),
                }),
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v3"),
                        typ: Type::TypeVar(TypeVar {
                            label: String::from("T"),
                        }),
                    },
                    position: position.clone(),
                }),
            ],
            formal_arguments: vec![
                LocalVar {
                    name: String::from("_v4"),
                    typ: Type::TypeVar(TypeVar {
                        label: String::from("E"),
                    }),
                },
                LocalVar {
                    name: String::from("_v5"),
                    typ: Type::TypeVar(TypeVar {
                        label: String::from("T"),
                    }),
                },
            ],
            return_type: Type::TypeVar(TypeVar {
                label: String::from("E"),
            }),
            position: position.clone(),
        });
        expected = Expr::FuncApp(FuncApp {
            function_name: String::from("f1"),
            arguments: vec![
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v2"),
                        typ: Type::Bool,
                    },
                    position: position.clone(),
                }),
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v3"),
                        typ: Type::Int,
                    },
                    position: position.clone(),
                }),
            ],
            formal_arguments: vec![
                LocalVar {
                    name: String::from("_v4"),
                    typ: Type::Bool,
                },
                LocalVar {
                    name: String::from("_v5"),
                    typ: Type::Int,
                },
            ],
            return_type: Type::Bool,
            position: position.clone(),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // DomainFuncApp
        source = Expr::DomainFuncApp(DomainFuncApp {
            domain_function: DomainFunc {
                name: String::from("df1"),
                formal_args: vec![
                    LocalVar {
                        name: String::from("_v2"),
                        typ: Type::TypeVar(TypeVar {
                            label: String::from("E"),
                        }),
                    },
                    LocalVar {
                        name: String::from("_v3"),
                        typ: Type::TypeVar(TypeVar {
                            label: String::from("T"),
                        }),
                    },
                ],
                return_type: Type::TypeVar(TypeVar {
                    label: String::from("T"),
                }),
                unique: false,
                domain_name: String::from("dn1"),
            },
            arguments: vec![
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v2"),
                        typ: Type::TypeVar(TypeVar {
                            label: String::from("E"),
                        }),
                    },
                    position: position.clone(),
                }),
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v3"),
                        typ: Type::TypeVar(TypeVar {
                            label: String::from("T"),
                        }),
                    },
                    position: position.clone(),
                }),
            ],
            position: position.clone(),
        });
        expected = Expr::DomainFuncApp(DomainFuncApp {
            domain_function: DomainFunc {
                name: String::from("df1"),
                formal_args: vec![
                    LocalVar {
                        name: String::from("_v2"),
                        typ: Type::Bool,
                    },
                    LocalVar {
                        name: String::from("_v3"),
                        typ: Type::Int,
                    },
                ],
                return_type: Type::Int,
                unique: false,
                domain_name: String::from("dn1"),
            },
            arguments: vec![
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v2"),
                        typ: Type::Bool,
                    },
                    position: position.clone(),
                }),
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v3"),
                        typ: Type::Int,
                    },
                    position: position.clone(),
                }),
            ],
            position: position.clone(),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // InhaleExhale
        source = Expr::InhaleExhale(InhaleExhale {
            inhale_expr: Box::new(
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v1"),
                        typ: Type::TypeVar(TypeVar {
                            label: String::from("T"),
                        }),
                    },
                    position: position.clone(),
            })),
            exhale_expr: Box::new(
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v2"),
                        typ: Type::TypeVar(TypeVar {
                            label: String::from("E"),
                        }),
                    },
                    position: position.clone(),
            })),
            position: position.clone(),
        });
        expected = Expr::InhaleExhale(InhaleExhale {
            inhale_expr: Box::new(
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v1"),
                        typ: Type::Int,
                    },
                    position: position.clone(),
            })),
            exhale_expr: Box::new(
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v2"),
                        typ: Type::Bool,
                    },
                    position: position.clone(),
            })),
            position: position.clone(),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // Downcast
        source = Expr::Downcast(DowncastExpr {
            base: Box::new(
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v1"),
                        typ: Type::TypeVar(TypeVar {
                            label: String::from("T"),
                        }),
                    },
                    position: position.clone(),
            })),
            enum_place: Box::new(
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v2"),
                        typ: Type::TypeVar(TypeVar {
                            label: String::from("E"),
                        }),
                    },
                    position: position.clone(),
            })),
            field: Field {
                name: String::from("f1"),
                typ: Type::TypeVar(TypeVar {
                    label: String::from("E"),
                }),
            },
        });
        expected = Expr::Downcast(DowncastExpr {
            base: Box::new(
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v1"),
                        typ: Type::Int,
                    },
                    position: position.clone(),
            })),
            enum_place: Box::new(
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v2"),
                        typ: Type::Bool,
                    },
                    position: position.clone(),
            })),
            field: Field {
                name: String::from("f1"),
                typ: Type::Bool,
            },
        });
        test(source, expected, &SUBSTITUTION_MAP);
    }

    #[test]
    // successful substitution within Stmt, going over all variants
    fn substitution_type_var_stmt_test() {
        // dummy position for convenient copying
        let position = Position::new(1, 2, 3);

        // Comment
        let mut source = Stmt::Comment(Comment {
            comment: String::from("c1"),
        });
        let mut expected = Stmt::Comment(Comment {
            comment: String::from("c1"),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // Label
        source = Stmt::Label(Label {
            label: String::from("c1"),
        });
        expected = Stmt::Label(Label {
            label: String::from("c1"),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // Inhale
        source = Stmt::Inhale(Inhale {
            expr: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::TypeVar(TypeVar {
                        label: String::from("T"),
                    }),
                },
                position: position.clone(),
            }),
        });
        expected = Stmt::Inhale(Inhale {
            expr: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::Int,
                },
                position: position.clone(),
            }),
        });
        test(source, expected, &SUBSTITUTION_MAP);


        // Exhale
        source = Stmt::Exhale(Exhale {
            expr: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::TypeVar(TypeVar {
                        label: String::from("T"),
                    }),
                },
                position: position.clone(),
            }),
            position: position.clone(),
        });
        expected = Stmt::Exhale(Exhale {
            expr: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::Int,
                },
                position: position.clone(),
            }),
            position: position.clone(),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // Assert
        source = Stmt::Assert(Assert {
            expr: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::TypeVar(TypeVar {
                        label: String::from("T"),
                    }),
                },
                position: position.clone(),
            }),
            position: position.clone(),
        });
        expected = Stmt::Assert(Assert {
            expr: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::Int,
                },
                position: position.clone(),
            }),
            position: position.clone(),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // MethodCall
        source = Stmt::MethodCall(MethodCall {
            method_name: String::from("m1"),
            arguments: vec![
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v2"),
                        typ: Type::TypeVar(TypeVar {
                            label: String::from("E"),
                        }),
                    },
                    position: position.clone(),
                }),
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v3"),
                        typ: Type::TypeVar(TypeVar {
                            label: String::from("T"),
                        }),
                    },
                    position: position.clone(),
                }),
            ],
            targets: vec![
                LocalVar {
                    name: String::from("_v4"),
                    typ: Type::TypeVar(TypeVar {
                        label: String::from("E"),
                    }),
                },
                LocalVar {
                    name: String::from("_v5"),
                    typ: Type::TypeVar(TypeVar {
                        label: String::from("T"),
                    }),
                },
            ],
        });
        expected = Stmt::MethodCall(MethodCall {
            method_name: String::from("m1"),
            arguments: vec![
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v2"),
                        typ: Type::Bool,
                    },
                    position: position.clone(),
                }),
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v3"),
                        typ: Type::Int,
                    },
                    position: position.clone(),
                }),
            ],
            targets: vec![
                LocalVar {
                    name: String::from("_v4"),
                    typ: Type::Bool,
                },
                LocalVar {
                    name: String::from("_v5"),
                    typ: Type::Int,
                },
            ],
        });
        test(source, expected, &SUBSTITUTION_MAP);

       // Assign
        source = Stmt::Assign(Assign {
            target: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::TypeVar(TypeVar {
                        label: String::from("E"),
                    }),
                },
                position: position.clone(),
            }),
            source: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v2"),
                    typ: Type::TypeVar(TypeVar {
                        label: String::from("T"),
                    }),
                },
                position: position.clone(),
            }),
            kind: AssignKind::SharedBorrow(Borrow(123)),
        });
        expected = Stmt::Assign(Assign {
            target: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::Bool,
                },
                position: position.clone(),
            }),
            source: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v2"),
                    typ: Type::Int,
                },
                position: position.clone(),
            }),
            kind: AssignKind::SharedBorrow(Borrow(123)),
        });
        test(source, expected, &SUBSTITUTION_MAP);

       // Fold
        source = Stmt::Fold(Fold {
            predicate_name: String::from("p1"),
            arguments: vec![
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v2"),
                        typ: Type::TypeVar(TypeVar {
                            label: String::from("E"),
                        }),
                    },
                    position: position.clone(),
                }),
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v3"),
                        typ: Type::TypeVar(TypeVar {
                            label: String::from("T"),
                        }),
                    },
                    position: position.clone(),
                }),
            ],
            permission: PermAmount::Write,
            enum_variant: Some(EnumVariantIndex::new(String::from("evi"))),
            position: position.clone(),
        });
        expected = Stmt::Fold(Fold {
            predicate_name: String::from("p1"),
            arguments: vec![
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v2"),
                        typ: Type::Bool,
                    },
                    position: position.clone(),
                }),
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v3"),
                        typ: Type::Int,
                    },
                    position: position.clone(),
                }),
            ],
            permission: PermAmount::Write,
            enum_variant: Some(EnumVariantIndex::new(String::from("evi"))),
            position: position.clone(),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // Unfold
        source = Stmt::Unfold(Unfold {
            predicate_name: String::from("p1"),
            arguments: vec![
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v2"),
                        typ: Type::TypeVar(TypeVar {
                            label: String::from("E"),
                        }),
                    },
                    position: position.clone(),
                }),
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v3"),
                        typ: Type::TypeVar(TypeVar {
                            label: String::from("T"),
                        }),
                    },
                    position: position.clone(),
                }),
            ],
            permission: PermAmount::Write,
            enum_variant: Some(EnumVariantIndex::new(String::from("evi"))),
        });
        expected = Stmt::Unfold(Unfold {
            predicate_name: String::from("p1"),
            arguments: vec![
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v2"),
                        typ: Type::Bool,
                    },
                    position: position.clone(),
                }),
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v3"),
                        typ: Type::Int,
                    },
                    position: position.clone(),
                }),
            ],
            permission: PermAmount::Write,
            enum_variant: Some(EnumVariantIndex::new(String::from("evi"))),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // Obtain
        source = Stmt::Obtain(Obtain {
            predicate_name: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::TypeVar(TypeVar {
                        label: String::from("T"),
                    }),
                },
                position: position.clone(),
            }),
            position: position.clone(),
        });
        expected = Stmt::Obtain(Obtain {
            predicate_name: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::Int,
                },
                position: position.clone(),
            }),
            position: position.clone(),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // BeinFrame
        source = Stmt::BeginFrame(BeginFrame {});
        expected = Stmt::BeginFrame(BeginFrame {});
        test(source, expected, &SUBSTITUTION_MAP);

        // EndFrame
        source = Stmt::EndFrame(EndFrame {});
        expected = Stmt::EndFrame(EndFrame {});
        test(source, expected, &SUBSTITUTION_MAP);

        // TransferPerm
        source = Stmt::TransferPerm(TransferPerm {
            left: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::TypeVar(TypeVar {
                        label: String::from("T"),
                    }),
                },
                position: position.clone(),
            }),
            right: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v2"),
                    typ: Type::TypeVar(TypeVar {
                        label: String::from("E"),
                    }),
                },
                position: position.clone(),
            }),
            unchecked: true,
        });
        expected = Stmt::TransferPerm(TransferPerm {
            left: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::Int,
                },
                position: position.clone(),
            }),
            right: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v2"),
                    typ: Type::Bool,
                },
                position: position.clone(),
            }),
            unchecked: true,
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // PackageMagicWand
        source = Stmt::PackageMagicWand(PackageMagicWand {
            magic_wand: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::TypeVar(TypeVar {
                        label: String::from("T"),
                    }),
                },
                position: position.clone(),
            }),
            package_stmts: vec![
                Stmt::Inhale(Inhale {
                    expr: Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v2"),
                            typ: Type::TypeVar(TypeVar {
                                label: String::from("T"),
                            }),
                        },
                        position: position.clone(),
                    }),
                }),
                Stmt::Exhale(Exhale {
                    expr: Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v3"),
                            typ: Type::TypeVar(TypeVar {
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
                LocalVar {
                    name: String::from("_v4"),
                    typ: Type::TypeVar(TypeVar {
                        label: String::from("T"),
                    }),
                },
                LocalVar {
                    name: String::from("_v5"),
                    typ: Type::TypeVar(TypeVar {
                        label: String::from("E"),
                    }),
                },
            ],
            position: position.clone(),
        });
        expected = Stmt::PackageMagicWand(PackageMagicWand {
            magic_wand: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::Int,
                },
                position: position.clone(),
            }),
            package_stmts: vec![
                Stmt::Inhale(Inhale {
                    expr: Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v2"),
                            typ: Type::Int,
                        },
                        position: position.clone(),
                    }),
                }),
                Stmt::Exhale(Exhale {
                    expr: Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v3"),
                            typ: Type::Bool,
                        },
                        position: position.clone(),
                    }),
                    position: position.clone(),
                })
            ],
            label: String::from("l1"),
            variables: vec![
                LocalVar {
                    name: String::from("_v4"),
                    typ: Type::Int,
                },
                LocalVar {
                    name: String::from("_v5"),
                    typ: Type::Bool,
                },
            ],
            position: position.clone(),
        });
        test(source, expected, &SUBSTITUTION_MAP);

       // ApplyMagicWand
        source = Stmt::ApplyMagicWand(ApplyMagicWand {
            magic_wand: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::TypeVar(TypeVar {
                        label: String::from("T"),
                    }),
                },
                position: position.clone(),
            }),
            position: position.clone(),
        });
        expected = Stmt::ApplyMagicWand(ApplyMagicWand {
            magic_wand: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::Int,
                },
                position: position.clone(),
            }),
            position: position.clone(),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // ExpireBorrows TODO: add this after DAG is checked
        source = Stmt::ExpireBorrows(ExpireBorrows {
            dag: DAG {
                borrow_indices: vec![(Borrow(1), 1), (Borrow(2), 2)].into_iter().collect(),
                nodes: vec![
                    Node {
                        guard: Expr::Local(Local {
                            variable: LocalVar {
                                name: String::from("_v1"),
                                typ: Type::TypeVar(TypeVar {
                                    label: String::from("T"),
                                }),
                            },
                            position: position.clone(),
                        }),
                        borrow: Borrow(123),
                        reborrowing_nodes: vec![Borrow(1), Borrow(2)],
                        reborrowed_nodes: vec![Borrow(1), Borrow(2)],
                        stmts: vec![
                            Stmt::Obtain(Obtain {
                                predicate_name: Expr::Local(Local {
                                    variable: LocalVar {
                                        name: String::from("_v2"),
                                        typ: Type::TypeVar(TypeVar {
                                            label: String::from("T"),
                                        }),
                                    },
                                    position: position.clone(),
                                }),
                                position: position.clone(),
                            }),
                            Stmt::Obtain(Obtain {
                                predicate_name: Expr::Local(Local {
                                    variable: LocalVar {
                                        name: String::from("_v3"),
                                        typ: Type::TypeVar(TypeVar {
                                            label: String::from("E"),
                                        }),
                                    },
                                    position: position.clone(),
                                }),
                                position: position.clone(),
                            }),
                        ],
                        borrowed_places: vec![
                            Expr::Local(Local {
                                variable: LocalVar {
                                    name: String::from("_v4"),
                                    typ: Type::TypeVar(TypeVar {
                                        label: String::from("T"),
                                    }),
                                },
                                position: position.clone(),
                            }),
                            Expr::Local(Local {
                                variable: LocalVar {
                                    name: String::from("_v5"),
                                    typ: Type::TypeVar(TypeVar {
                                        label: String::from("E"),
                                    }),
                                },
                                position: position.clone(),
                            }),
                        ],
                        conflicting_borrows: vec![Borrow(403), Borrow(404)],
                        alive_conflicting_borrows: vec![Borrow(1403), Borrow(1404)],
                        place: Some(Expr::Local(Local {
                            variable: LocalVar {
                                name: String::from("_v6"),
                                typ: Type::TypeVar(TypeVar {
                                    label: String::from("T"),
                                }),
                            },
                            position: position.clone(),
                        })),
                    }
                ],
                borrowed_places: vec![
                    Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v7"),
                            typ: Type::TypeVar(TypeVar {
                                label: String::from("T"),
                            }),
                        },
                        position: position.clone(),
                    }),
                    Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v8"),
                            typ: Type::TypeVar(TypeVar {
                                label: String::from("E"),
                            }),
                        },
                        position: position.clone(),
                    })
                ],
            },
        });
        expected = Stmt::ExpireBorrows(ExpireBorrows {
            dag: DAG {
                borrow_indices: vec![(Borrow(1), 1), (Borrow(2), 2)].into_iter().collect(),
                nodes: vec![
                    Node {
                        guard: Expr::Local(Local {
                            variable: LocalVar {
                                name: String::from("_v1"),
                                typ: Type::Int,
                            },
                            position: position.clone(),
                        }),
                        borrow: Borrow(123),
                        reborrowing_nodes: vec![Borrow(1), Borrow(2)],
                        reborrowed_nodes: vec![Borrow(1), Borrow(2)],
                        stmts: vec![
                            Stmt::Obtain(Obtain {
                                predicate_name: Expr::Local(Local {
                                    variable: LocalVar {
                                        name: String::from("_v2"),
                                        typ: Type::Int,
                                    },
                                    position: position.clone(),
                                }),
                                position: position.clone(),
                            }),
                            Stmt::Obtain(Obtain {
                                predicate_name: Expr::Local(Local {
                                    variable: LocalVar {
                                        name: String::from("_v3"),
                                        typ: Type::Bool,
                                    },
                                    position: position.clone(),
                                }),
                                position: position.clone(),
                            }),
                        ],
                        borrowed_places: vec![
                            Expr::Local(Local {
                                variable: LocalVar {
                                    name: String::from("_v4"),
                                    typ: Type::Int,
                                },
                                position: position.clone(),
                            }),
                            Expr::Local(Local {
                                variable: LocalVar {
                                    name: String::from("_v5"),
                                    typ: Type::Bool,
                                },
                                position: position.clone(),
                            }),
                        ],
                        conflicting_borrows: vec![Borrow(403), Borrow(404)],
                        alive_conflicting_borrows: vec![Borrow(1403), Borrow(1404)],
                        place: Some(Expr::Local(Local {
                            variable: LocalVar {
                                name: String::from("_v6"),
                                typ: Type::Int,
                            },
                            position: position.clone(),
                        })),
                    }
                ],
                borrowed_places: vec![
                    Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v7"),
                            typ: Type::Int,
                        },
                        position: position.clone(),
                    }),
                    Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v8"),
                            typ: Type::Bool,
                        },
                        position: position.clone(),
                    })
                ],
            },
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // If
        source = Stmt::If(If {
            guard: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::TypeVar(TypeVar {
                        label: String::from("T"),
                    }),
                },
                position: position.clone(),
            }),
            then_stmts: vec![
                Stmt::Inhale(Inhale {
                    expr: Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v2"),
                            typ: Type::TypeVar(TypeVar {
                                label: String::from("T"),
                            }),
                        },
                        position: position.clone(),
                    }),
                }),
                Stmt::Exhale(Exhale {
                    expr: Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v3"),
                            typ: Type::TypeVar(TypeVar {
                                label: String::from("E"),
                            }),
                        },
                        position: position.clone(),
                    }),
                    position: position.clone(),
                })
            ],
            else_stmts: vec![
                Stmt::Inhale(Inhale {
                    expr: Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v4"),
                            typ: Type::TypeVar(TypeVar {
                                label: String::from("T"),
                            }),
                        },
                        position: position.clone(),
                    }),
                }),
                Stmt::Exhale(Exhale {
                    expr: Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v5"),
                            typ: Type::TypeVar(TypeVar {
                                label: String::from("E"),
                            }),
                        },
                        position: position.clone(),
                    }),
                    position: position.clone(),
                })
            ],
        });
        expected = Stmt::If(If {
            guard: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::Int,
                },
                position: position.clone(),
            }),
            then_stmts: vec![
                Stmt::Inhale(Inhale {
                    expr: Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v2"),
                            typ: Type::Int,
                        },
                        position: position.clone(),
                    }),
                }),
                Stmt::Exhale(Exhale {
                    expr: Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v3"),
                            typ: Type::Bool,
                        },
                        position: position.clone(),
                    }),
                    position: position.clone(),
                })
            ],
            else_stmts: vec![
                Stmt::Inhale(Inhale {
                    expr: Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v4"),
                            typ: Type::Int,
                        },
                        position: position.clone(),
                    }),
                }),
                Stmt::Exhale(Exhale {
                    expr: Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v5"),
                            typ: Type::Bool,
                        },
                        position: position.clone(),
                    }),
                    position: position.clone(),
                })
            ],
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // Downcast
        source = Stmt::Downcast(Downcast {
            base: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::Int,
                },
                position: position.clone(),
            }),
            field: Field {
                name: String::from("f1"),
                typ: Type::Bool,
            }
        });
        expected = Stmt::Downcast(Downcast {
            base: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::Int,
                },
                position: position.clone(),
            }),
            field: Field {
                name: String::from("f1"),
                typ: Type::Bool,
            }
        });
        test(source, expected, &SUBSTITUTION_MAP);
    }

    #[test]
    // successful substitution within BodylessMethod
    fn substitution_type_var_bodyless_method_test() {
        let source = BodylessMethod {
            name: String::from("bm1"),
            formal_args: vec![
                LocalVar {
                    name: String::from("_v1"),
                    typ: Type::TypeVar(TypeVar {
                        label: String::from("T"),
                    }),
                },
                LocalVar {
                    name: String::from("_v2"),
                    typ: Type::TypeVar(TypeVar {
                        label: String::from("D"),
                    }),
                },
            ],
            formal_returns: vec![
                LocalVar {
                    name: String::from("_r"),
                    typ: Type::TypedRef(TypedRef {
                        label: String::from("CustomStruct"),
                        arguments: vec![
                            Type::TypeVar(TypeVar {
                                label: String::from("E"),
                            }),
                            Type::TypeVar(TypeVar {
                                label: String::from("F"),
                            }),
                        ],
                    }),
                }
            ],
        };

        let expected = BodylessMethod {
            name: String::from("bm1"),
            formal_args: vec![
                LocalVar {
                    name: String::from("_v1"),
                    typ: Type::Int,
                },
                LocalVar {
                    name: String::from("_v2"),
                    typ: Type::TypeVar(TypeVar {
                        label: String::from("D"),
                    }),
                },
            ],
            formal_returns: vec![
                LocalVar {
                    name: String::from("_r"),
                    typ: Type::TypedRef(TypedRef {
                        label: String::from("CustomStruct"),
                        arguments: vec![
                            Type::Bool,
                            Type::TypedRef(TypedRef {
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
        let source = DomainFunc {
            name: String::from("df"),
            formal_args: vec![
                LocalVar {
                    name: String::from("_v1"),
                    typ: Type::Int,
                },
                LocalVar {
                    name: String::from("_v2"),
                    typ: Type::TypeVar(TypeVar {
                        label: String::from("D"),
                    }),
                },
            ],
            return_type: Type::TypeVar(TypeVar {
                label: String::from("T"),
            }),
            unique: true,
            domain_name: String::from("dn"),
        };

        let expected = DomainFunc {
            name: String::from("df"),
            formal_args: vec![
                LocalVar {
                    name: String::from("_v1"),
                    typ: Type::Int,
                },
                LocalVar {
                    name: String::from("_v2"),
                    typ: Type::TypeVar(TypeVar {
                        label: String::from("D"),
                    }),
                },
            ],
            return_type: Type::Int,
            unique: true,
            domain_name: String::from("dn"),
        };
        test(source, expected, &SUBSTITUTION_MAP);
    }

    #[test]
    // successful substitution within DomainAxiom
    fn substitution_type_var_domain_axiom_test() {
        // dummy position for convenient copying
        let position = Position::new(1, 2, 3);

        let source = DomainAxiom {
            name: String::from("da"),
            expr: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::TypeVar(TypeVar {
                        label: String::from("T"),
                    }),
                },
                position: position.clone(),
            }),
            domain_name: String::from("dn"),
        };

        let expected = DomainAxiom {
            name: String::from("da"),
            expr: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::Int,
                },
                position: position.clone(),
            }),
            domain_name: String::from("dn"),
        };
        test(source, expected, &SUBSTITUTION_MAP);
    }

    #[test]
    // successful substitution within Domain
    fn substitution_type_var_domain_test() {
        // dummy position for convenient copying
        let position = Position::new(1, 2, 3);

        let source = Domain {
            name: String::from("domain"),
            functions: vec![
                DomainFunc {
                    name: String::from("df1"),
                    formal_args: vec![
                        LocalVar {
                            name: String::from("_v1"),
                            typ: Type::Int,
                        },
                        LocalVar {
                            name: String::from("_v2"),
                            typ: Type::TypeVar(TypeVar {
                                label: String::from("D"),
                            }),
                        },
                    ],
                    return_type: Type::TypeVar(TypeVar {
                        label: String::from("T"),
                    }),
                    unique: true,
                    domain_name: String::from("dn1"),
                },
                DomainFunc {
                    name: String::from("df2"),
                    formal_args: vec![
                        LocalVar {
                            name: String::from("_v3"),
                            typ: Type::Int,
                        },
                        LocalVar {
                            name: String::from("_v4"),
                            typ: Type::TypeVar(TypeVar {
                                label: String::from("C"),
                            }),
                        },
                    ],
                    return_type: Type::TypeVar(TypeVar {
                        label: String::from("E"),
                    }),
                    unique: true,
                    domain_name: String::from("dn2"),
                }
            ],
            axioms: vec![
                DomainAxiom {
                    name: String::from("da1"),
                    expr: Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v5"),
                            typ: Type::TypeVar(TypeVar {
                                label: String::from("T"),
                            }),
                        },
                        position: position.clone(),
                    }),
                    domain_name: String::from("dn3"),
                },
                DomainAxiom {
                    name: String::from("da2"),
                    expr: Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v6"),
                            typ: Type::TypeVar(TypeVar {
                                label: String::from("E"),
                            }),
                        },
                        position: position.clone(),
                    }),
                    domain_name: String::from("dn4"),
                }
            ],
            type_vars: vec![
                Type::TypeVar(TypeVar {
                    label: String::from("T"),
                }),
                Type::TypeVar(TypeVar {
                    label: String::from("E"),
                }),
            ]
        };

        let expected = Domain {
            name: String::from("domain"),
            functions: vec![
                DomainFunc {
                    name: String::from("df1"),
                    formal_args: vec![
                        LocalVar {
                            name: String::from("_v1"),
                            typ: Type::Int,
                        },
                        LocalVar {
                            name: String::from("_v2"),
                            typ: Type::TypeVar(TypeVar {
                                label: String::from("D"),
                            }),
                        },
                    ],
                    return_type: Type::Int,
                    unique: true,
                    domain_name: String::from("dn1"),
                },
                DomainFunc {
                    name: String::from("df2"),
                    formal_args: vec![
                        LocalVar {
                            name: String::from("_v3"),
                            typ: Type::Int,
                        },
                        LocalVar {
                            name: String::from("_v4"),
                            typ: Type::TypeVar(TypeVar {
                                label: String::from("C"),
                            }),
                        },
                    ],
                    return_type: Type::Bool,
                    unique: true,
                    domain_name: String::from("dn2"),
                }
            ],
            axioms: vec![
                DomainAxiom {
                    name: String::from("da1"),
                    expr: Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v5"),
                            typ: Type::Int,
                        },
                        position: position.clone(),
                    }),
                    domain_name: String::from("dn3"),
                },
                DomainAxiom {
                    name: String::from("da2"),
                    expr: Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v6"),
                            typ: Type::Bool,
                        },
                        position: position.clone(),
                    }),
                    domain_name: String::from("dn4"),
                }
            ],
            type_vars: vec![
                Type::Int,
                Type::Bool,
            ]
        };
        test(source, expected, &SUBSTITUTION_MAP);
    }

    #[test]
    // successful substitution within Function
    fn substitution_type_var_function_test() {
        // dummy position for convenient copying
        let position = Position::new(1, 2, 3);

        let source = Function {
            name: String::from("f1"),
            formal_args: vec![
                LocalVar {
                    name: String::from("_v1"),
                    typ: Type::Int,
                },
                LocalVar {
                    name: String::from("_v2"),
                    typ: Type::Bool,
                },
            ],
            return_type: Type::TypeVar(TypeVar {
                label: String::from("T"),
            }),
            pres: vec![
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v3"),
                        typ: Type::Int,
                    },
                    position: position.clone(),
                }),
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v4"),
                        typ: Type::Bool,
                    },
                    position: position.clone(),
                }),
            ],
            posts: vec![
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v5"),
                        typ: Type::Int,
                    },
                    position: position.clone(),
                }),
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v6"),
                        typ: Type::Bool,
                    },
                    position: position.clone(),
                }),
            ],
            body: Some(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v7"),
                    typ: Type::Int,
                },
                position: position.clone(),
            })),
        };

        let expected = Function {
            name: String::from("f1"),
            formal_args: vec![
                LocalVar {
                    name: String::from("_v1"),
                    typ: Type::Int,
                },
                LocalVar {
                    name: String::from("_v2"),
                    typ: Type::Bool,
                },
            ],
            return_type: Type::Int,
            pres: vec![
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v3"),
                        typ: Type::Int,
                    },
                    position: position.clone(),
                }),
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v4"),
                        typ: Type::Bool,
                    },
                    position: position.clone(),
                }),
            ],
            posts: vec![
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v5"),
                        typ: Type::Int,
                    },
                    position: position.clone(),
                }),
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v6"),
                        typ: Type::Bool,
                    },
                    position: position.clone(),
                }),
            ],
            body: Some(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v7"),
                    typ: Type::Int,
                },
                position: position.clone(),
            })),
        };
        test(source, expected, &SUBSTITUTION_MAP);
    }

    #[test]
    // successful substitution within StructPredicate
    fn substitution_type_var_struct_predicate_test() {
        // dummy position for convenient copying
        let position = Position::new(1, 2, 3);

        let source = StructPredicate {
            name: String::from("sp1"),
            this: LocalVar {
                name: String::from("_v1"),
                typ: Type::TypeVar(TypeVar {
                    label: String::from("T"),
                }),
            },
            body: Some(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v7"),
                    typ: Type::TypeVar(TypeVar {
                        label: String::from("E"),
                    }),
                },
                position: position.clone(),
            })),
        };

        let expected = StructPredicate {
            name: String::from("sp1"),
            this: LocalVar {
                name: String::from("_v1"),
                typ: Type::Int,
            },
            body: Some(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v7"),
                    typ: Type::Bool,
                },
                position: position.clone(),
            })),
        };
        test(source, expected, &SUBSTITUTION_MAP);
    }

    #[test]
    // successful substitution within EnumPredicate
    fn substitution_type_var_enum_predicate_test() {
        // dummy position for convenient copying
        let position = Position::new(1, 2, 3);

        let source = EnumPredicate {
            name: String::from("ep1"),
            this: LocalVar {
                name: String::from("_v1"),
                typ: Type::TypeVar(TypeVar {
                    label: String::from("T"),
                }),
            },
            discriminant_field: Field {
                name: String::from("f1"),
                typ: Type::TypeVar(TypeVar {
                    label: String::from("E"),
                }),
            },
            discriminant_bounds: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v2"),
                    typ: Type::TypeVar(TypeVar {
                        label: String::from("E"),
                    }),
                },
                position: position.clone(),
            }),
            variants: vec![
                (
                    Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v3"),
                            typ: Type::TypeVar(TypeVar {
                                label: String::from("T"),
                            }),
                        },
                        position: position.clone(),
                    }),
                    String::from("variant1"),
                    StructPredicate {
                        name: String::from("sp1"),
                        this: LocalVar {
                            name: String::from("_v4"),
                            typ: Type::TypeVar(TypeVar {
                                label: String::from("E"),
                            }),
                        },
                        body: Some(Expr::Local(Local {
                            variable: LocalVar {
                                name: String::from("_v5"),
                                typ: Type::TypeVar(TypeVar {
                                    label: String::from("T"),
                                }),
                            },
                            position: position.clone(),
                        })),
                    },
                ),
                (
                    Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v6"),
                            typ: Type::TypeVar(TypeVar {
                                label: String::from("T"),
                            }),
                        },
                        position: position.clone(),
                    }),
                    String::from("variant1"),
                    StructPredicate {
                        name: String::from("sp1"),
                        this: LocalVar {
                            name: String::from("_v7"),
                            typ: Type::TypeVar(TypeVar {
                                label: String::from("E"),
                            }),
                        },
                        body: Some(Expr::Local(Local {
                            variable: LocalVar {
                                name: String::from("_v8"),
                                typ: Type::TypeVar(TypeVar {
                                    label: String::from("T"),
                                }),
                            },
                            position: position.clone(),
                        })),
                    },
                ),
            ]
        };

        let expected = EnumPredicate {
            name: String::from("ep1"),
            this: LocalVar {
                name: String::from("_v1"),
                typ: Type::Int,
            },
            discriminant_field: Field {
                name: String::from("f1"),
                typ: Type::Bool,
            },
            discriminant_bounds: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v2"),
                    typ: Type::Bool,
                },
                position: position.clone(),
            }),
            variants: vec![
                (
                    Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v3"),
                            typ: Type::Int,
                        },
                        position: position.clone(),
                    }),
                    String::from("variant1"),
                    StructPredicate {
                        name: String::from("sp1"),
                        this: LocalVar {
                            name: String::from("_v4"),
                            typ: Type::Bool,
                        },
                        body: Some(Expr::Local(Local {
                            variable: LocalVar {
                                name: String::from("_v5"),
                                typ: Type::Int,
                            },
                            position: position.clone(),
                        })),
                    },
                ),
                (
                    Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v6"),
                            typ: Type::Int,
                        },
                        position: position.clone(),
                    }),
                    String::from("variant1"),
                    StructPredicate {
                        name: String::from("sp1"),
                        this: LocalVar {
                            name: String::from("_v7"),
                            typ: Type::Bool,
                        },
                        body: Some(Expr::Local(Local {
                            variable: LocalVar {
                                name: String::from("_v8"),
                                typ: Type::Int,
                            },
                            position: position.clone(),
                        })),
                    },
                ),
            ]
        };
        test(source, expected, &SUBSTITUTION_MAP);
    }

    #[test]
    // successful substitution within Predicate, going over all variants
    fn substitution_type_var_predicate_test() {
        // dummy position for convenient copying
        let position = Position::new(1, 2, 3);

        // Struct
        let mut source = Predicate::Struct(StructPredicate {
            name: String::from("sp1"),
            this: LocalVar {
                name: String::from("_v4"),
                typ: Type::TypeVar(TypeVar {
                    label: String::from("E"),
                }),
            },
            body: Some(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v5"),
                    typ: Type::TypeVar(TypeVar {
                        label: String::from("T"),
                    }),
                },
                position: position.clone(),
            })),
        });
        let mut expected = Predicate::Struct(StructPredicate {
            name: String::from("sp1"),
            this: LocalVar {
                name: String::from("_v4"),
                typ: Type::Bool,
            },
            body: Some(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v5"),
                    typ: Type::Int,
                },
                position: position.clone(),
            })),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // Enum
        source = Predicate::Enum(EnumPredicate {
            name: String::from("ep1"),
            this: LocalVar {
                name: String::from("_v1"),
                typ: Type::TypeVar(TypeVar {
                    label: String::from("T"),
                }),
            },
            discriminant_field: Field {
                name: String::from("f1"),
                typ: Type::TypeVar(TypeVar {
                    label: String::from("E"),
                }),
            },
            discriminant_bounds: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v2"),
                    typ: Type::TypeVar(TypeVar {
                        label: String::from("E"),
                    }),
                },
                position: position.clone(),
            }),
            variants: vec![
                (
                    Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v3"),
                            typ: Type::TypeVar(TypeVar {
                                label: String::from("T"),
                            }),
                        },
                        position: position.clone(),
                    }),
                    String::from("variant1"),
                    StructPredicate {
                        name: String::from("sp1"),
                        this: LocalVar {
                            name: String::from("_v4"),
                            typ: Type::TypeVar(TypeVar {
                                label: String::from("E"),
                            }),
                        },
                        body: Some(Expr::Local(Local {
                            variable: LocalVar {
                                name: String::from("_v5"),
                                typ: Type::TypeVar(TypeVar {
                                    label: String::from("T"),
                                }),
                            },
                            position: position.clone(),
                        })),
                    },
                ),
                (
                    Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v6"),
                            typ: Type::TypeVar(TypeVar {
                                label: String::from("T"),
                            }),
                        },
                        position: position.clone(),
                    }),
                    String::from("variant1"),
                    StructPredicate {
                        name: String::from("sp1"),
                        this: LocalVar {
                            name: String::from("_v7"),
                            typ: Type::TypeVar(TypeVar {
                                label: String::from("E"),
                            }),
                        },
                        body: Some(Expr::Local(Local {
                            variable: LocalVar {
                                name: String::from("_v8"),
                                typ: Type::TypeVar(TypeVar {
                                    label: String::from("T"),
                                }),
                            },
                            position: position.clone(),
                        })),
                    },
                ),
            ]
        });
        expected = Predicate::Enum(EnumPredicate {
            name: String::from("ep1"),
            this: LocalVar {
                name: String::from("_v1"),
                typ: Type::Int,
            },
            discriminant_field: Field {
                name: String::from("f1"),
                typ: Type::Bool,
            },
            discriminant_bounds: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v2"),
                    typ: Type::Bool,
                },
                position: position.clone(),
            }),
            variants: vec![
                (
                    Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v3"),
                            typ: Type::Int,
                        },
                        position: position.clone(),
                    }),
                    String::from("variant1"),
                    StructPredicate {
                        name: String::from("sp1"),
                        this: LocalVar {
                            name: String::from("_v4"),
                            typ: Type::Bool,
                        },
                        body: Some(Expr::Local(Local {
                            variable: LocalVar {
                                name: String::from("_v5"),
                                typ: Type::Int,
                            },
                            position: position.clone(),
                        })),
                    },
                ),
                (
                    Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v6"),
                            typ: Type::Int,
                        },
                        position: position.clone(),
                    }),
                    String::from("variant1"),
                    StructPredicate {
                        name: String::from("sp1"),
                        this: LocalVar {
                            name: String::from("_v7"),
                            typ: Type::Bool,
                        },
                        body: Some(Expr::Local(Local {
                            variable: LocalVar {
                                name: String::from("_v8"),
                                typ: Type::Int,
                            },
                            position: position.clone(),
                        })),
                    },
                ),
            ]
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // Bodyless
        source = Predicate::Bodyless(
            String::from("b1"),
            LocalVar {
                name: String::from("_v1"),
                typ: Type::TypeVar(TypeVar {
                    label: String::from("T"),
                }),
            },
        );

        expected = Predicate::Bodyless(
            String::from("b1"),
            LocalVar {
                name: String::from("_v1"),
                typ: Type::Int,
            },
        );
        test(source, expected, &SUBSTITUTION_MAP);
    }

    #[test]
    // successful substitution within Trigger
    fn substitution_type_var_trigger_test() {
        // dummy position for convenient copying
        let position = Position::new(1, 2, 3);

        let source = Trigger::new(
            vec![
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v1"),
                        typ: Type::TypeVar(TypeVar {
                            label: String::from("T"),
                        }),
                    },
                    position: position.clone(),
                }),
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v2"),
                        typ: Type::TypeVar(TypeVar {
                            label: String::from("E"),
                        }),
                    },
                    position: position.clone(),
                }),
            ]
        );
        let expected = Trigger::new(
            vec![
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v1"),
                        typ: Type::Int,
                    },
                    position: position.clone(),
                }),
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v2"),
                        typ: Type::Bool,
                    },
                    position: position.clone(),
                }),
            ]
        );
        test(source, expected, &SUBSTITUTION_MAP);
    }

    #[test]
    // successful substitution within CfgBlockIndex
    fn substitution_type_var_cfg_block_index_test() {
        // dummy position for convenient copying
        let uuid = Uuid::new_v4();

        let source = CfgBlockIndex {
            method_uuid: uuid,
            block_index: 123,
        };
        let expected = CfgBlockIndex {
            method_uuid: uuid,
            block_index: 123,
        };
        test(source, expected, &SUBSTITUTION_MAP);
    }

    #[test]
    // successful substitution within Successor, going over all variants
    fn substitution_type_var_successor_test() {
        // dummy uuid and position for convenient copying
        let uuid = Uuid::new_v4();
        let position = Position::new(1, 2, 3);

        // Undefined
        let mut source = Successor::Undefined;
        let mut expected = Successor::Undefined;
        test(source, expected, &SUBSTITUTION_MAP);

        // Return
        source = Successor::Return;
        expected = Successor::Return;
        test(source, expected, &SUBSTITUTION_MAP);

        // Goto
        source = Successor::Goto(
            CfgBlockIndex {
                method_uuid: uuid,
                block_index: 123,
            }
        );
        expected = Successor::Goto(
            CfgBlockIndex {
                method_uuid: uuid,
                block_index: 123,
            }
        );
        test(source, expected, &SUBSTITUTION_MAP);

        // GotoSwitch
        source = Successor::GotoSwitch(
            vec![
                (Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v1"),
                        typ: Type::TypeVar(TypeVar {
                            label: String::from("T"),
                        }),
                    },
                    position: position.clone(),
                }), CfgBlockIndex {
                    method_uuid: uuid,
                    block_index: 1,
                }),
                (Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v2"),
                        typ: Type::TypeVar(TypeVar {
                            label: String::from("E"),
                        }),
                    },
                    position: position.clone(),
                }), CfgBlockIndex {
                    method_uuid: uuid,
                    block_index: 2,
                }),
            ],
            CfgBlockIndex {
                method_uuid: uuid,
                block_index: 123,
            }
        );
        expected = Successor::GotoSwitch(
            vec![
                (Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v1"),
                        typ: Type::Int,
                    },
                    position: position.clone(),
                }), CfgBlockIndex {
                    method_uuid: uuid,
                    block_index: 1,
                }),
                (Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v2"),
                        typ: Type::Bool,
                    },
                    position: position.clone(),
                }), CfgBlockIndex {
                    method_uuid: uuid,
                    block_index: 2,
                }),
            ],
            CfgBlockIndex {
                method_uuid: uuid,
                block_index: 123,
            }
        );
        test(source, expected, &SUBSTITUTION_MAP);
    }


    #[test]
    // successful substitution within CfgBlock
    fn substitution_type_var_cfg_block_test() {
        // dummy uuid and position for convenient copying
        let uuid = Uuid::new_v4();
        let position = Position::new(1, 2, 3);

        let source = CfgBlock {
            stmts: vec![
                Stmt::Obtain(Obtain {
                    predicate_name: Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v1"),
                            typ: Type::TypeVar(TypeVar {
                                label: String::from("T"),
                            }),
                        },
                        position: position.clone(),
                    }),
                    position: position.clone(),
                }),
                Stmt::Obtain(Obtain {
                    predicate_name: Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v2"),
                            typ: Type::TypeVar(TypeVar {
                                label: String::from("E"),
                            }),
                        },
                        position: position.clone(),
                    }),
                    position: position.clone(),
                }),
            ],
            successor: Successor::GotoSwitch(
                vec![
                    (Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v3"),
                            typ: Type::TypeVar(TypeVar {
                                label: String::from("T"),
                            }),
                        },
                        position: position.clone(),
                    }), CfgBlockIndex {
                        method_uuid: uuid,
                        block_index: 1,
                    }),
                    (Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v4"),
                            typ: Type::TypeVar(TypeVar {
                                label: String::from("E"),
                            }),
                        },
                        position: position.clone(),
                    }), CfgBlockIndex {
                        method_uuid: uuid,
                        block_index: 2,
                    }),
                ],
                CfgBlockIndex {
                    method_uuid: uuid,
                    block_index: 123,
                }
            ),
        };
        let expected = CfgBlock {
            stmts: vec![
                Stmt::Obtain(Obtain {
                    predicate_name: Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v1"),
                            typ: Type::Int,
                        },
                        position: position.clone(),
                    }),
                    position: position.clone(),
                }),
                Stmt::Obtain(Obtain {
                    predicate_name: Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v2"),
                            typ: Type::Bool,
                        },
                        position: position.clone(),
                    }),
                    position: position.clone(),
                }),
            ],
            successor: Successor::GotoSwitch(
                vec![
                    (Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v3"),
                            typ: Type::Int,
                        },
                        position: position.clone(),
                    }), CfgBlockIndex {
                        method_uuid: uuid,
                        block_index: 1,
                    }),
                    (Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v4"),
                            typ: Type::Bool,
                        },
                        position: position.clone(),
                    }), CfgBlockIndex {
                        method_uuid: uuid,
                        block_index: 2,
                    }),
                ],
                CfgBlockIndex {
                    method_uuid: uuid,
                    block_index: 123,
                }
            ),
        };
        test(source, expected, &SUBSTITUTION_MAP);
    }

    #[test]
    // successful substitution within CfgMethod
    fn substitution_type_var_cfg_method_test() {
        // dummy uuid and position for convenient copying
        let uuid = Uuid::new_v4();
        let position = Position::new(1, 2, 3);

        let source = CfgMethod {
            uuid: uuid,
            method_name: String::from("mn1"),
            formal_arg_count: 5,
            formal_returns: vec![
                LocalVar {
                    name: String::from("_v1"),
                    typ: Type::TypeVar(TypeVar {
                        label: String::from("T"),
                    }),
                },
                LocalVar {
                    name: String::from("_v2"),
                    typ: Type::TypeVar(TypeVar {
                        label: String::from("E"),
                    }),
                }
            ],
            local_vars: vec![
                LocalVar {
                    name: String::from("_v3"),
                    typ: Type::TypeVar(TypeVar {
                        label: String::from("T"),
                    }),
                },
                LocalVar {
                    name: String::from("_v4"),
                    typ: Type::TypeVar(TypeVar {
                        label: String::from("E"),
                    }),
                }
            ],
            labels: vec![String::from("l1"), String::from("l2")].into_iter().collect(),
            reserved_labels: vec![String::from("rl1"), String::from("rl2")].into_iter().collect(),
            basic_blocks: vec![
                CfgBlock {
                    stmts: vec![
                        Stmt::Obtain(Obtain {
                            predicate_name: Expr::Local(Local {
                                variable: LocalVar {
                                    name: String::from("_v1"),
                                    typ: Type::TypeVar(TypeVar {
                                        label: String::from("T"),
                                    }),
                                },
                                position: position.clone(),
                            }),
                            position: position.clone(),
                        }),
                        Stmt::Obtain(Obtain {
                            predicate_name: Expr::Local(Local {
                                variable: LocalVar {
                                    name: String::from("_v2"),
                                    typ: Type::TypeVar(TypeVar {
                                        label: String::from("E"),
                                    }),
                                },
                                position: position.clone(),
                            }),
                            position: position.clone(),
                        }),
                    ],
                    successor: Successor::GotoSwitch(
                        vec![
                            (Expr::Local(Local {
                                variable: LocalVar {
                                    name: String::from("_v3"),
                                    typ: Type::TypeVar(TypeVar {
                                        label: String::from("T"),
                                    }),
                                },
                                position: position.clone(),
                            }), CfgBlockIndex {
                                method_uuid: uuid,
                                block_index: 1,
                            }),
                            (Expr::Local(Local {
                                variable: LocalVar {
                                    name: String::from("_v4"),
                                    typ: Type::TypeVar(TypeVar {
                                        label: String::from("E"),
                                    }),
                                },
                                position: position.clone(),
                            }), CfgBlockIndex {
                                method_uuid: uuid,
                                block_index: 2,
                            }),
                        ],
                        CfgBlockIndex {
                            method_uuid: uuid,
                            block_index: 123,
                        }
                    ),
                }
            ],
            basic_blocks_labels: vec![String::from("bbl1"), String::from("bbl2")],
            fresh_var_index: 1,
            fresh_label_index: 2,
        };
        let expected = CfgMethod {
            uuid: uuid,
            method_name: String::from("mn1"),
            formal_arg_count: 5,
            formal_returns: vec![
                LocalVar {
                    name: String::from("_v1"),
                    typ: Type::Int,
                },
                LocalVar {
                    name: String::from("_v2"),
                    typ: Type::Bool,
                }
            ],
            local_vars: vec![
                LocalVar {
                    name: String::from("_v3"),
                    typ: Type::Int,
                },
                LocalVar {
                    name: String::from("_v4"),
                    typ: Type::Bool,
                }
            ],
            labels: vec![String::from("l1"), String::from("l2")].into_iter().collect(),
            reserved_labels: vec![String::from("rl1"), String::from("rl2")].into_iter().collect(),
            basic_blocks: vec![
                CfgBlock {
                    stmts: vec![
                        Stmt::Obtain(Obtain {
                            predicate_name: Expr::Local(Local {
                                variable: LocalVar {
                                    name: String::from("_v1"),
                                    typ: Type::Int,
                                },
                                position: position.clone(),
                            }),
                            position: position.clone(),
                        }),
                        Stmt::Obtain(Obtain {
                            predicate_name: Expr::Local(Local {
                                variable: LocalVar {
                                    name: String::from("_v2"),
                                    typ: Type::Bool,
                                },
                                position: position.clone(),
                            }),
                            position: position.clone(),
                        }),
                    ],
                    successor: Successor::GotoSwitch(
                        vec![
                            (Expr::Local(Local {
                                variable: LocalVar {
                                    name: String::from("_v3"),
                                    typ: Type::Int,
                                },
                                position: position.clone(),
                            }), CfgBlockIndex {
                                method_uuid: uuid,
                                block_index: 1,
                            }),
                            (Expr::Local(Local {
                                variable: LocalVar {
                                    name: String::from("_v4"),
                                    typ: Type::Bool,
                                },
                                position: position.clone(),
                            }), CfgBlockIndex {
                                method_uuid: uuid,
                                block_index: 2,
                            }),
                        ],
                        CfgBlockIndex {
                            method_uuid: uuid,
                            block_index: 123,
                        }
                    ),
                }
            ],
            basic_blocks_labels: vec![String::from("bbl1"), String::from("bbl2")],
            fresh_var_index: 1,
            fresh_label_index: 2,
        };
        test(source, expected, &SUBSTITUTION_MAP);
    }

    #[test]
    // successful substitution within Node
    fn substitution_type_var_node_test() {
        // dummy position for convenient copying
        let position = Position::new(1, 2, 3);

        let source = Node {
            guard: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::TypeVar(TypeVar {
                        label: String::from("T"),
                    }),
                },
                position: position.clone(),
            }),
            borrow: Borrow(123),
            reborrowing_nodes: vec![Borrow(1), Borrow(2)],
            reborrowed_nodes: vec![Borrow(1), Borrow(2)],
            stmts: vec![
                Stmt::Obtain(Obtain {
                    predicate_name: Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v2"),
                            typ: Type::TypeVar(TypeVar {
                                label: String::from("T"),
                            }),
                        },
                        position: position.clone(),
                    }),
                    position: position.clone(),
                }),
                Stmt::Obtain(Obtain {
                    predicate_name: Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v3"),
                            typ: Type::TypeVar(TypeVar {
                                label: String::from("E"),
                            }),
                        },
                        position: position.clone(),
                    }),
                    position: position.clone(),
                }),
            ],
            borrowed_places: vec![
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v4"),
                        typ: Type::TypeVar(TypeVar {
                            label: String::from("T"),
                        }),
                    },
                    position: position.clone(),
                }),
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v5"),
                        typ: Type::TypeVar(TypeVar {
                            label: String::from("E"),
                        }),
                    },
                    position: position.clone(),
                }),
            ],
            conflicting_borrows: vec![Borrow(403), Borrow(404)],
            alive_conflicting_borrows: vec![Borrow(1403), Borrow(1404)],
            place: Some(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v6"),
                    typ: Type::TypeVar(TypeVar {
                        label: String::from("T"),
                    }),
                },
                position: position.clone(),
            })),
        };

        let expected = Node {
            guard: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::Int,
                },
                position: position.clone(),
            }),
            borrow: Borrow(123),
            reborrowing_nodes: vec![Borrow(1), Borrow(2)],
            reborrowed_nodes: vec![Borrow(1), Borrow(2)],
            stmts: vec![
                Stmt::Obtain(Obtain {
                    predicate_name: Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v2"),
                            typ: Type::Int,
                        },
                        position: position.clone(),
                    }),
                    position: position.clone(),
                }),
                Stmt::Obtain(Obtain {
                    predicate_name: Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v3"),
                            typ: Type::Bool,
                        },
                        position: position.clone(),
                    }),
                    position: position.clone(),
                }),
            ],
            borrowed_places: vec![
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v4"),
                        typ: Type::Int,
                    },
                    position: position.clone(),
                }),
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v5"),
                        typ: Type::Bool,
                    },
                    position: position.clone(),
                }),
            ],
            conflicting_borrows: vec![Borrow(403), Borrow(404)],
            alive_conflicting_borrows: vec![Borrow(1403), Borrow(1404)],
            place: Some(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v6"),
                    typ: Type::Int,
                },
                position: position.clone(),
            })),
        };

        test(source, expected, &SUBSTITUTION_MAP);
    }

    #[test]
    // successful substitution within DAG
    fn substitution_type_var_dag_test() {
        // dummy position for convenient copying

        let position = Position::new(1, 2, 3);

        let source = DAG {
            borrow_indices: vec![(Borrow(1), 1), (Borrow(2), 2)].into_iter().collect(),
            nodes: vec![
                Node {
                    guard: Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v1"),
                            typ: Type::TypeVar(TypeVar {
                                label: String::from("T"),
                            }),
                        },
                        position: position.clone(),
                    }),
                    borrow: Borrow(123),
                    reborrowing_nodes: vec![Borrow(1), Borrow(2)],
                    reborrowed_nodes: vec![Borrow(1), Borrow(2)],
                    stmts: vec![
                        Stmt::Obtain(Obtain {
                            predicate_name: Expr::Local(Local {
                                variable: LocalVar {
                                    name: String::from("_v2"),
                                    typ: Type::TypeVar(TypeVar {
                                        label: String::from("T"),
                                    }),
                                },
                                position: position.clone(),
                            }),
                            position: position.clone(),
                        }),
                        Stmt::Obtain(Obtain {
                            predicate_name: Expr::Local(Local {
                                variable: LocalVar {
                                    name: String::from("_v3"),
                                    typ: Type::TypeVar(TypeVar {
                                        label: String::from("E"),
                                    }),
                                },
                                position: position.clone(),
                            }),
                            position: position.clone(),
                        }),
                    ],
                    borrowed_places: vec![
                        Expr::Local(Local {
                            variable: LocalVar {
                                name: String::from("_v4"),
                                typ: Type::TypeVar(TypeVar {
                                    label: String::from("T"),
                                }),
                            },
                            position: position.clone(),
                        }),
                        Expr::Local(Local {
                            variable: LocalVar {
                                name: String::from("_v5"),
                                typ: Type::TypeVar(TypeVar {
                                    label: String::from("E"),
                                }),
                            },
                            position: position.clone(),
                        }),
                    ],
                    conflicting_borrows: vec![Borrow(403), Borrow(404)],
                    alive_conflicting_borrows: vec![Borrow(1403), Borrow(1404)],
                    place: Some(Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v6"),
                            typ: Type::TypeVar(TypeVar {
                                label: String::from("T"),
                            }),
                        },
                        position: position.clone(),
                    })),
                }
            ],
            borrowed_places: vec![
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v7"),
                        typ: Type::TypeVar(TypeVar {
                            label: String::from("T"),
                        }),
                    },
                    position: position.clone(),
                }),
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v8"),
                        typ: Type::TypeVar(TypeVar {
                            label: String::from("E"),
                        }),
                    },
                    position: position.clone(),
                })
            ],
        };

        let expected = DAG {
            borrow_indices: vec![(Borrow(1), 1), (Borrow(2), 2)].into_iter().collect(),
            nodes: vec![
                Node {
                    guard: Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v1"),
                            typ: Type::Int,
                        },
                        position: position.clone(),
                    }),
                    borrow: Borrow(123),
                    reborrowing_nodes: vec![Borrow(1), Borrow(2)],
                    reborrowed_nodes: vec![Borrow(1), Borrow(2)],
                    stmts: vec![
                        Stmt::Obtain(Obtain {
                            predicate_name: Expr::Local(Local {
                                variable: LocalVar {
                                    name: String::from("_v2"),
                                    typ: Type::Int,
                                },
                                position: position.clone(),
                            }),
                            position: position.clone(),
                        }),
                        Stmt::Obtain(Obtain {
                            predicate_name: Expr::Local(Local {
                                variable: LocalVar {
                                    name: String::from("_v3"),
                                    typ: Type::Bool,
                                },
                                position: position.clone(),
                            }),
                            position: position.clone(),
                        }),
                    ],
                    borrowed_places: vec![
                        Expr::Local(Local {
                            variable: LocalVar {
                                name: String::from("_v4"),
                                typ: Type::Int,
                            },
                            position: position.clone(),
                        }),
                        Expr::Local(Local {
                            variable: LocalVar {
                                name: String::from("_v5"),
                                typ: Type::Bool,
                            },
                            position: position.clone(),
                        }),
                    ],
                    conflicting_borrows: vec![Borrow(403), Borrow(404)],
                    alive_conflicting_borrows: vec![Borrow(1403), Borrow(1404)],
                    place: Some(Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v6"),
                            typ: Type::Int,
                        },
                        position: position.clone(),
                    })),
                }
            ],
            borrowed_places: vec![
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v7"),
                        typ: Type::Int,
                    },
                    position: position.clone(),
                }),
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v8"),
                        typ: Type::Bool,
                    },
                    position: position.clone(),
                })
            ],
        };
        test(source, expected, &SUBSTITUTION_MAP);
    }
}
