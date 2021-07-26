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
}
