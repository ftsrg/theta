This project wraps the legacy [Z3 solver](https://github.com/Z3Prover/z3) into our common interfaces for solvers (located in the [solver](../solver) project).
Normally, only the factory class should be used from this project to instantiate a new solver and then the common interfaces should be preferred.

The version of Z3 that was used for building the legacy libraries can be found under [this](https://github.com/Z3Prover/z3/tree/z3-4.3.2) branch of a Z3 fork. There are automatic releases for the branch.
Overview of the patches to upstream Z3 (tag 4.5.0):

* Replaced library names with z3legacy
* Replaced package name with z3legacy
* Patched the hwf.cpp to compile on windows
