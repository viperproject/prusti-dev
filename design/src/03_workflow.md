# Verification Work-Flow

The `prusti` crate implements a Rust compiler driver that drives the
verification process. The high-level flow of verifying a single crate is
as follows:

1.  The driver parses and type-checks the program with specifications.
    More information on parsing and type-checking specifications
    can be found [here](./03_specifications.html).
2.  The driver creates a verifier instance defined in crate
    `prusti-viper` by first creating
    `prusti_interface::verifier::VerifierBuilder` and then
    `prusti_interface::verifier::Verifier`.
3.  The driver collects all procedures in the crate being verified,
    creates a verification task and passes it to the verifier together
    with a reference to itself (it uses the
    `prusti_interface::environment::Environment` facade).
4.  Verifier constructs a Viper program by querying the driver via
    environment facade, passes it to the verification back-end, gets
    results, emits errors (if any), and reports the status back to the
    driver. The types for communication between `prusti-viper` and
    `prusti` are defined in the crate `prusti_interface`.

## Query Oriented Design

This section described the query oriented design, which is used in the
Rust compiler itself, `prusti`, and `prusti-viper`.

TODO: Describe the query based design.
