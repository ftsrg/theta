This project contains the analysis algorithms and their components, e.g., abstract domains, abstract
reachability graphs, refinement strategies, precisions, etc. The formalism specific components (
e.g., the interpreter) are implemented in separate projects for the given formalism.

## Further reading

The full publication list is at [theta.mit.bme.hu/publications](https://theta.mit.bme.hu/publications/).

**CEGAR**

* [A Configurable CEGAR Framework with Interpolation-based Refinements](https://doi.org/10.1007/978-3-319-39570-8_11) (FORTE 2016) — the configurable CEGAR framework this project implements.
* [Efficient Strategies for CEGAR-based Model Checking](https://doi.org/10.1007/s10817-019-09535-x) (JAR 2020) — the reference paper for the configuration options; see also [CEGAR-algorithms.md](../../../doc/CEGAR-algorithms.md).
* [A Survey on CEGAR-based Model Checking](https://theta.mit.bme.hu/publications/hajduaMsc2015.pdf) (MSc, 2015).
* [Exploratory Analysis of the Performance of a Configurable CEGAR Framework](https://doi.org/10.5281/zenodo.291895) (Minisy 2017) and [A Preliminary Analysis on the Effect of Randomness in a CEGAR Framework](https://theta.mit.bme.hu/publications/minisy2018.pdf) (Minisy 2018) — how configuration and randomness affect performance.

**Abstract domains** (`expl/`, `pred/`, `prod2/`)

* [Software Model Checking with a Combination of Explicit Values and Predicates](https://doi.org/10.5281/zenodo.2597969) (Minisy 2019).
* [Combining Abstract Domains for Software Model Checking](https://theta.mit.bme.hu/publications/bajkaidBsc2018.pdf) (BSc, 2018) and [Efficient combinations of predicate abstraction and explicit-value analysis](https://theta.mit.bme.hu/publications/bajkaidMsc2020.pdf) (MSc, 2020).

**Beyond CEGAR** (`algorithm/ic3`, `algorithm/mdd`, `algorithm/bounded`)

* [Applying Incremental, Inductive Model Checking to Software](https://theta.mit.bme.hu/publications/tegzestBsc2018.pdf) (BSc, 2018) — IC3 on software, via a transformation to a symbolic transition system.
* [EmergenTheta: Variations on Symbolic Transition Systems](https://theta.mit.bme.hu/publications/tacas2025emergentheta.pdf) (SV-COMP 2025) — the monolithic-expression encodings shared by BMC/k-induction/IMC, IC3 and MDD.
* [EmergenTheta: Experimental Analyses within the Theta Framework](https://doi.org/10.1007/978-3-032-22749-2_25) (SV-COMP 2026) — combined predicate-explicit domain, on-the-fly reachability and counterexample generation for generalized saturation, and an IC3 backend.

**Liveness / LTL** (`algorithm/loopchecker`, `multi/`)

* [Abstraction-Based Model Checking of Linear Temporal Properties](https://theta.mit.bme.hu/publications/minisy2020mm.pdf) (Minisy 2020) — CEGAR combined with automata-theoretic LTL checking, and the interpolation-based refinement of lasso-shaped counterexamples.

**Runtime monitoring** (`runtimemonitor/`)

* [Extending the Capabilities of the CEGAR Model Checking Algorithm](https://theta.mit.bme.hu/publications/adamzsMsc2023.pdf) (MSc, 2023) — detecting and mitigating non-progressing refinement loops.

**Pointers** (`ptr/`)

* [Giving Some Pointers for Abstraction-Based Model Checking](https://doi.org/10.3311/MINISY2025-002) (Minisy 2025) — tracking predicates over abstract memory locations.
