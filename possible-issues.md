# Possible issues

Suspected bugs and smells found while working on the code, not yet addressed.

- `pthread-join-result/lookup-wrong-key` gets a wrong `false` for `valid-memsafety`, at the dereference of the joined result.
- `weaver-mutants/chl-chromosome-{subst-v1,opt-symm-v2,trans-v1}` get a wrong `true` for `valid-memsafety`. In `subst-v1`, the overrun of `o_2[4]` goes through `safe_malloc`, whose `void *` binding keeps the bound in bytes under the cell models.
- `ExprSimplifier.simplifyOr` returns true for a disjunction without operands, whereas evaluating `Or()` is false by definition. `MemsafetyPass.flatDerefCheck` guards against it.
- With a pointee type `MallocFunctionPass` cannot determine, the allocation bound stays in bytes under the cell models, which can miss an overrun.
- The Z3 user propagator crashes natively (`conflict_resolution::eq2literals`) if the first check after encoding is an OC exit query under a solver scope, e.g. on `pthread-complex/safestack_relacy` with `--oc-decision-procedure PROPAGATOR`. `XcfaOcChecker` avoids this by discharging dead targets only for the IDL procedure.
