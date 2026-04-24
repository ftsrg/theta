This project wraps the [Eldarica HORN solver](https://github.com/uuverifiers/eldarica/) into our common interfaces for
solvers (located in the [solver](../solver) project).
Normally, only the factory class should be used from this project to instantiate a new solver and
then the common interfaces should be preferred.