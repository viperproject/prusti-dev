Analysis
========

Intra-procedural static analysis of MIR functions.

Each analysis compute a state for each program point:
* `DefinitelyInitializedAnalysis` computes the places that are definitely initialized. By enabling a flag, this analysis also considers "initialized" the places of `Copy` types after a *move* operation.
* `ReachingDefinitionAnalysis` computes for each local variable the set of assignments or function arguments from which the value of the local variable might come from.
* `MaybeBorrowedAnalysis` computes the places that are blocked due to a mutable reference or frozen due to a shared reference.
* `DefinitelyAccessibleAnalysis` computes the places that are are surely owned (i.e. can be borrowed by a mutable reference) or accessible (i.e. can be borrowed by a shared reference).
