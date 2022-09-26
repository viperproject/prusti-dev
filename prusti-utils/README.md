# Prusti-utils

Common compiler-agnostic utilities used across the Prusti project.

The difference between this crate and prusti-common is that
prusti-common dynamically links to the JVM, whereas prusti-utils does
not. This allows using prusti-utils from prusti-launch.
