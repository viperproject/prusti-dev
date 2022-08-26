# Computation of an interface between Prusti and Rustc 

Run with the feature flag ``dump_operational_pcs`` to compute. 

Details of the free PCS repacking are outlined in ``src/joins/README.md``. 

## TODO

 - [x] Straight line, unshared code
    - [x] refactor
    - [x] 1-ary propagation method (repacker)
        - [x] temporaries
        - [x] uninit
        - [x] apply-packing
        - [x] separating union
        - [x] refactor
        - [x] fix lifetimes
        - [x] change pcs-after back to pcs-before again
    - [ ] stable output representation for testing
        - [ ] serialization
    - [ ] formalize poset interpretation of places
    - [x] MIR -> MicroMIR translation
    - [ ] graphviz output
    - [ ] test harness
        - [ ] tests
 - [x] Branches
    - [x] implement conditional elaboration
        - [x] repacker
            - [x] operational description of conditional joins
            - [ ] common PCS transformation interface (repack interface)
        - [x] straight line translation
        - [x] terminator translation
        - [ ] eager drops (trim to unique join footprint)
            - [x] implement before_statement for analysis results
            - [ ] kills in terms of before_statement of parent MIR place
        - [x] eager dependent repacks (to maximal, identical, point)
        - [x] runtime checks of packing invariants
    - [ ] reread our init and alloc rules, make sure hoare semantics is coherent with them
        - [x] fix unconditional drop incoherence
        - [ ] pack uninits?
    - [ ] loops?
    - [ ] check: analysis_as_permission might not be granular enough
    - [ ] refactor joins out from conditional mod
        - [ ] add single packer and single unpacker
        - [ ] add weakeners
 - [x] Borrows 
    - [x] add type dependency to hoare semantics
    - [ ] refactor the joins/ module (sprint is done)
    - [ ] finish documenting the rationale for joins 

- Issues
 - [ ] When more than one field of a struct 
    - [ ] implement footprint computation
        - [ ] should uninits be packable? packable but not unpackable?
 - [ ] Inside loops kill elaboration fails
    - [ ] should a place be accessible in a loop before it's first loop use?

- Maintainence
    - [ ] refactor out common data structures
    - [x] hoare semantics trait has Option baked in (why?), remove this 
    - [x] add explicit precondition to kill syntax
    - [ ] retranslate ``return``, ``_0`` only when returning a value?
        - [ ] (semi-urgent) remove u _0 hack for place lookup
        - [ ] translation missing initial PCS (eg. function arguments)
    - [x] conditional translation incorrect
        - [x] missing blocks (pretty printing)
        - [x] missing some conditional jumps
        - [x] unsoundness in postconditions
    - [ ] traversal during translation which ignores unwind paths
        - [ ] remove ``resume`` translation hack
    - [ ] refactor to use placeSet
        - [ ] singleton_permission_set
