## Overview

Frontend for constrained Horn clauses (CHCs). Theta solves CHCs by transforming them into a control
flow automaton ([`cfa`](../../cfa/cfa/README.md)) and analysing it with the framework's existing
algorithms; it has participated in CHC-COMP since 2023.

## Further reading

The full publication list is at [theta.mit.bme.hu/publications](https://theta.mit.bme.hu/publications/).

* [Theta as a Horn Solver](http://dx.doi.org/10.4204/EPTCS.434.5) (HCVS 2025) — describes the algorithms Theta employs for CHCs and analyses its strengths and weaknesses on the CHC-COMP benchmarks.
* [Bottoms Up for CHCs: Novel Transformation of Linear Constrained Horn Clauses to Software Verification](https://doi.org/10.4204/eptcs.402.11) (HCVS 2023) — a bottom-up transformation of linear CHCs, which more than doubled the number of solved tasks compared to the top-down technique.
* [Abstraction Based Techniques for Constrained Horn Clause Solving](https://theta.mit.bme.hu/publications/somorjaimBsc2022.pdf) (BSc, 2022) — applies abstraction-refinement-based model checking to CHC solving.
* [Learning and Synthesis Supported Software Verification](https://theta.mit.bme.hu/publications/tegzestMsc2020.pdf) (MSc, 2020) — adapts Horn clause solver algorithms to invariant synthesis, with samples that can represent infinitely many states.
