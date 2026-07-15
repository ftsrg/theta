## Overview

This project contains the Uppaal timed automata (XTA) formalism. Its main purpose is to describe
timed systems as graphs with clock variables. A domain specific language (DSL) is available to parse
XTAs from the textual representation of Uppaal. The project contains:

* Classes to represent XTAs.
* A domain specific language (DSL) to parse XTAs from a textual representation.

### Related projects

* [`xta-analysis`](../xta-analysis/README.md): XTA specific analysis modules enabling the algorithms
  to operate on them.
* [`xta-cli`](../xta-cli/README.md): An executable tool (command line) for running analyses on XTAs.

## Further reading

The full publication list is at [theta.mit.bme.hu/publications](https://theta.mit.bme.hu/publications/).

**Lazy abstraction for clocks**

* [Lazy Reachability Checking for Timed Automata using Interpolants](https://doi.org/10.1007/978-3-319-65765-3_15) (FORMATS 2017) — zone interpolation to strengthen the abstraction.
* [Lazy Reachability Checking for Timed Automata with Discrete Variables](https://doi.org/10.1007/978-3-319-94111-0_14) (SPIN 2018) — combining data abstraction with lazy abstraction for clocks.
* [Configurable verification of timed automata with discrete variables](https://doi.org/10.1007/s00236-020-00393-4) (Acta Informatica 2020) — the configurable framework, integrating LU-bound-based lazy abstraction; the journal version of the line above.
* [Timed Automata Verification using Interpolants](https://doi.org/10.5281/zenodo.291907) (Minisy 2017) — interpolation over difference bound matrices.
* [Generalizing lazy abstraction refinement algorithms with partial orders](https://theta.mit.bme.hu/publications/cziborovadBsc2021.pdf) (BSc, 2021) — a configurable lazy abstraction framework built on partial orders and Galois connections.

**Other refinement strategies**

* [Backward reachability analysis for timed automata with data variables](https://doi.org/10.14279/tuj.eceasst.76.1076) (AVoCS 2018) — handling data variables with the weakest precondition operation.
* [Activity-Based Abstraction Refinement for Timed Systems](https://doi.org/10.5281/zenodo.291891) (Minisy 2017) — refinement tailored to clock variables.
* [Verification of Timed Automata by CEGAR-Based Algorithms](https://theta.mit.bme.hu/publications/farkasrMsc2016.pdf) (MSc, 2016).

**Models, benchmarks and applications**

* [Formal Modeling of Real-Time Systems with Data Processing](https://theta.mit.bme.hu/publications/minisy2016tt.pdf) (Minisy 2016) — a formalism covering both timing and data.
* [Towards Reliable Benchmarks of Timed Automata](https://theta.mit.bme.hu/publications/minisy2018fr.pdf) (Minisy 2018) — the benchmark suite used to compare these algorithms.
* [Abstraction-based timed model checking for software-intensive system models](https://theta.mit.bme.hu/publications/cziborovadMsc2023.pdf) (MSc, 2023) — timed verification without discretization.
