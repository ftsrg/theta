# Tool variants

Theta is submitted to competitions under several tool names. They are packaging variants of
`xcfa-cli`, differing in the portfolio they run and the solvers they ship (see the `variant { … }`
blocks in [`xcfa-cli/build.gradle.kts`](../subprojects/xcfa/xcfa-cli/build.gradle.kts)); the
archived artifacts are linked from the [repository README](../README.md).

| Tool | Variant | Portfolio |
|---|---|---|
| Theta | `Theta-svcomp` | the default [portfolio](Portfolio.md) of abstraction-refinement analyses |
| EmergenTheta | `EmergenTheta-svcomp` | emerging (not yet mature) analyses |
| Thorn | `Thorn-svcomp` | `--portfolio HORN`: software verification via CHC encoding (Eldarica, Golem, Z3) |
| ThetaCHC | `Theta-chccomp` | CHC-COMP entry; see [`chc-frontend`](../subprojects/frontends/chc-frontend/README.md) |

## Further reading

The full publication list is at [theta.mit.bme.hu/publications](https://theta.mit.bme.hu/publications/).

* [EmergenTheta: Verification Beyond Abstraction Refinement](https://doi.org/10.1007/978-3-031-57256-2_23) (SV-COMP 2024) — why EmergenTheta exists: a sandbox separating emerging techniques from the mature ones, so that new approaches can be tried without hurting the reliability of the main tool.
* [EmergenTheta: Variations on Symbolic Transition Systems](https://theta.mit.bme.hu/publications/tacas2025emergentheta.pdf) (SV-COMP 2025).
* [EmergenTheta: Experimental Analyses within the Theta Framework](https://doi.org/10.1007/978-3-032-22749-2_25) (SV-COMP 2026) — first submission to all categories.
* [Theta: Abstraction Based Techniques for Verifying Concurrency](https://doi.org/10.1007/978-3-031-57256-2_30) (SV-COMP 2024) and [Theta: Various Approaches for Concurrent Program Verification](https://doi.org/10.1007/978-3-031-90660-2_22) (SV-COMP 2025).
* [Theta as a Horn Solver](http://dx.doi.org/10.4204/EPTCS.434.5) (HCVS 2025) — ThetaCHC in CHC-COMP.
