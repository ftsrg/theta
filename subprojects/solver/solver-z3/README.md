This project wraps the [Z3 solver](https://github.com/Z3Prover/z3) into our common interfaces for
solvers (located in the [solver](../solver) project).
Normally, only the factory class should be used from this project to instantiate a new solver and
then the common interfaces should be preferred.