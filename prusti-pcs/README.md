# Computation of an interface between Prusti and Rustc 

Run with the feature flag ``dump_operational_pcs`` to compute. 

## TODO

 - [ ] Straight line, unshared code
    - [x] 1-ary propagation method
        - [ ] temporaries
        - [ ] uninit
    - [ ] formalize poset interpretation of places
    - [ ] MIR -> MicroMIR translation
    - [ ] unify straight-line code 
    - [ ] stable output representation for testing
        - [ ] graphviz output
    - [ ] test harness
        - [ ] tests