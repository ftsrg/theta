This project wraps the [JavaSMT solver wrapper](https://github.com/sosy-lab/java-smt) into our common interfaces for solvers (located in the [solver](../solver) project).
Normally, only the factory class should be used from this project to instantiate a new solver and then the common interfaces should be preferred.

Known limitations:

* No array literal and function application support
* Some expressions do not work:
  * mkInt2Real
  * mkBVRotateLeft
  * mkBVRotateRight
  * mkFPRem
  * floating point literal from bitvectors
  * bitvector modulo creates rem

Various issues and/or PRs are expected to be filed in the JavaSMT upstream repo, so these will eventually be fixed.