# XCFA procedure passes

A pass rewrites one procedure of an XCFA after it is built and before an analysis sees it.
`ProcedurePassManager` fixes the sequence and groups it into phases; `CPasses` is the sequence used
for C input, and the other managers (`NontermValidationPasses`, `ChcPasses`, `Btor2Passes`,
`LitmusPasses`) are smaller selections from the same set.

**The order is part of the contract.** Several passes are only correct in a particular position, and
the comments in `ProcedurePassManager` state the constraint at each such point.

## The C pipeline

Each phase below is one group in `CPasses`, in order.

| phase | passes | what happens | depends on |
|---|---|---|---|
| formatting | `NormalizePass`, `DeterministicPass` | put edge labels in the sequence-of-flat-labels shape every later pass assumes, and make branching deterministic | nothing; almost everything below depends on **them** -- several passes assert `metaData["deterministic"]` |
| | `EmptyEdgeRemovalPass`, `UnusedLocRemovalPass` | drop do-nothing edges and locations not reachable from the entry | after `NormalizePass` |
| | `ErrorLocationPass`, `AssertionToErrorLocationPass`, `FinalLocationPass` | give the procedure the error and final locations the checked property needs | before anything that redirects edges into those locations (`MemsafetyPass`, `DataRaceToReachabilityPass`) |
| | `SvCompIntrinsicsPass`, `FpFunctionsToExprsPass` | lower `__VERIFIER_*` and the floating-point builtins to expressions | before the call-consuming passes below |
| | `PthreadArrayHandleUnrollPass` | unroll `for (i…) pthread_create(&t[i], …)` so the handle index is a constant | **before `CLibraryFunctionsPass`**, which rejects a non-constant handle index, and **before `ReferenceElimination`**, which folds `&t[i]` away. There is no `SimplifyExprsPass` this early, which is why it substitutes the loop variable itself |
| | `CLibraryFunctionsPass`, `AtomicFunctionsPass` | model the pthread and `_Atomic`/`__atomic_*` families as XCFA labels | before `ReferenceElimination`: they read `&x` arguments as references |
| | `LibraryStubsPass` | model the stdio/string calls nothing defines | **before `ReferenceElimination`**: a written pointer argument must still be `&x`, because a folded base id no longer carries its pointee type and the stub would then silently write nothing. **Before the instrumentation phase**, or the writes it does emit are never checked for races or memory safety. After `CLibraryFunctionsPass`, which flags the calls it handles itself |
| memory | `ReferenceElimination` | give every address-taken object a base id, turning `&x` into a pointer value and `*p` into a dereference | after every pass that needs to see a reference (all of group 1) |
| | `CallocFunctionPass` | lower `calloc` to `malloc` + `memset` | before `MallocFunctionPass` and `MemoryFunctionsPass`, which model the two halves |
| | `MallocFunctionPass`, `AllocaFunctionPass` | turn allocation calls into assignments out of the shared base counter | after the frontend published its static-base high-water mark, so the counter is seeded past it |
| optimizing | `SimplifyExprsPass`, `UnrollPass`, `EmptyEdgeRemovalPass` | constant-fold, then unroll loops (and expand recursion, when a recursion bound is set) | `UnrollPass` needs **a `SimplifyExprsPass` after it** (the one in the cleanup phase) to fold the loop variable into the copies it made |
| calls | `FunctionPointerCallsPass` | expand a call through a function pointer into a dispatch over its candidates | before `InlineProceduresPass`, so the direct calls it produces can be inlined |
| | `InlineProceduresPass`, `NondetFunctionPass`, `InlinedProcedureRemovalPass` | inline what can be inlined, model `__VERIFIER_nondet_*`, drop the bodies left behind | removal after inlining |
| | `ReferenceElimination` (again) | inlining binds `&…` arguments to parameters only now, and no reference may reach the analyses | after `InlineProceduresPass` |
| cleanup | `EmptyEdgeRemovalPass`, `SimplifyExprsPass`, `UnusedLocRemovalPass`, `RemoveDeadEnds`, `EliminateSelfLoops`, `StaticCoiPass` | shrink the CFA before the instrumentation below multiplies it | `StaticCoiPass` after inlining; `SimplifyExprsPass` is also what folds `UnrollPass`'s copies |
| instrumentation | `NarrowCellRangePass` | constrain a narrow cell's value to what its C type can hold | before `MemsafetyPass` and `OverflowDetectionPass`, which read those cells |
| | `MemsafetyPass`, `NoSideEffectPass`, `HavocPromotionAndRange` | build the memory-safety guards and clean up what they leave | after every pass that creates a dereference to guard |
| | `LbePass` (+ `NormalizePass`, `DeterministicPass`) | large-block encoding | re-normalize after it: it re-shapes labels |
| | the witness pass, if a witness is being applied or validated | | after `LbePass`'s re-normalization |
| | `DataRaceToReachabilityPass`, `OverflowDetectionPass` | reduce the data-race and overflow properties to reachability | **after every pass that creates a memory access**, or that access is not instrumented and the property is silently under-checked |
| | `MemoryFunctionsPass` | spell out `memcpy`/`memset`/`memmove` over the destination's cells | before anything that havocs the same objects, i.e. before `UnresolvedInvokeToHavocPass` |
| | `UnresolvedInvokeToHavocPass` | havoc whatever calls are left | **last** of the call-consuming passes, by definition |
| memory model | `FlatMemoryPass`, `ByteMemoryPass` | fold `(base, offset)` to one flat address, then split wide cells into bytes; both no-ops unless their `--memory-model` is selected | after every pass that creates or rewrites a dereference; `ByteMemoryPass` after `FlatMemoryPass` |
| final | `UnusedVarPass`, `EmptyEdgeRemovalPass`, `UnusedLocRemovalPass` | drop what the instrumentation made dead | last |

Passes not in this pipeline are used by individual backends: `MutexToVarPass`,
`AssumeFalseRemovalPass`, `AtomicReadsOneWritePass` and `WitnessOptimizer` by the OC checker,
`SsaPass`/`NoUninitVar`/`HavocToUninitVar` by the monolithic and Horn adapters, and
`DereferenceToArrayPass` by the backends that want memory as arrays rather than as dereferences.

## Rules the passes follow

- **`UnrollPass` runs early**, so a loop a later pass *emits* (a symbolic-length fill, a nondet fill
  over a large region) is never unrolled and reaches the analyses as a real loop. Unrolling those is
  not a better answer but no answer at all.
- **A havoc is bounded to the C type it writes.** A bare havoc is unconstrained across its whole SMT
  sort -- under integer arithmetic, the unbounded integers -- so it can hand back a value no object
  of that type could hold. See `withinTypeRange`.
- **Havoc rather than leave stale.** Where a write is only partly modelled (a straddled tail cell, a
  region a stub writes through a pointer), the affected cells are havoc'd. Unconstrained is a safe
  over-approximation; the old value is one specific wrong value.
- **Refuse loudly rather than model approximately.** A tool error scores nothing under SV-COMP; a
  wrong answer scores much worse. A pass that cannot state a construct exactly declines it, and logs
  why -- the call is then left in place and surfaces later as "No such method ...".
- **A pass leaves the builder consistent.** Every edge must run between two locations the procedure
  still lists; `ProcedurePass.runChecked` asserts this after each pass, so run passes through it.

See also [`c2xcfa`](../../../../../../../../../../c2xcfa/README.md) for how objects, cells and the
memory models are represented, which several of these passes depend on.
