# XCFA procedure passes

A pass rewrites one procedure of an XCFA after it is built and before an analysis sees it.
`ProcedurePassManager` fixes the sequence and groups it into phases; `CPasses` is the sequence used
for C input, and the other managers (`NontermValidationPasses`, `ChcPasses`, `Btor2Passes`,
`LitmusPasses`) are smaller selections from the same set.

**The order is part of the contract.** Several passes are only correct in a particular position, and
the comments in `ProcedurePassManager` state the constraint at each such point.

## The C pipeline

Each phase below is one group in `CPasses`, in order.

| phase | passes | what happens |
|---|---|---|
| formatting | `NormalizePass`, `DeterministicPass` | put edge labels in the sequence-of-flat-labels shape every later pass assumes, and make branching deterministic |
| | `EmptyEdgeRemovalPass`, `UnusedLocRemovalPass` | drop do-nothing edges and locations not reachable from the entry |
| | `ErrorLocationPass`, `AssertionToErrorLocationPass`, `FinalLocationPass` | give the procedure the error and final locations the checked property needs |
| | `SvCompIntrinsicsPass`, `FpFunctionsToExprsPass` | lower `__VERIFIER_*` and the floating-point builtins to expressions |
| | `PthreadArrayHandleUnrollPass`, `CLibraryFunctionsPass`, `AtomicFunctionsPass` | model the pthread and `_Atomic`/`__atomic_*` families as XCFA labels |
| memory | `ReferenceElimination` | give every address-taken object a base id, turning `&x` into a pointer value and `*p` into a dereference |
| | `CallocFunctionPass`, `MallocFunctionPass`, `AllocaFunctionPass` | turn allocation calls into assignments out of the shared base counter |
| optimizing | `SimplifyExprsPass`, `UnrollPass`, `EmptyEdgeRemovalPass` | constant-fold, then unroll loops (and expand recursion, when a recursion bound is set) |
| calls | `FunctionPointerCallsPass` | expand a call through a function pointer into a dispatch over its candidates |
| | `InlineProceduresPass`, `NondetFunctionPass`, `InlinedProcedureRemovalPass` | inline what can be inlined, model `__VERIFIER_nondet_*`, drop the bodies left behind |
| | `ReferenceElimination` (again) | inlining binds `&…` arguments to parameters only now, and no reference may reach the analyses |
| cleanup | `EmptyEdgeRemovalPass`, `SimplifyExprsPass`, `UnusedLocRemovalPass`, `RemoveDeadEnds`, `EliminateSelfLoops`, `StaticCoiPass` | shrink the CFA before the instrumentation below multiplies it |
| instrumentation | `NarrowCellRangePass` | constrain a narrow cell's value to what its C type can hold, before the guards read it |
| | `MemsafetyPass`, `NoSideEffectPass`, `HavocPromotionAndRange` | build the memory-safety guards and clean up what they leave |
| | `LbePass` (+ `NormalizePass`, `DeterministicPass`) | large-block encoding, which re-shapes labels and so must be re-normalized |
| | the witness pass, if a witness is being applied or validated | |
| | `DataRaceToReachabilityPass`, `OverflowDetectionPass` | reduce the data-race and overflow properties to reachability |
| | `MemoryFunctionsPass` | spell out `memcpy`/`memset`/`memmove` over the destination's cells |
| | `LibraryStubsPass`, `UnresolvedInvokeToHavocPass` | model, then havoc, the calls nothing above consumed |
| memory model | `FlatMemoryPass`, `ByteMemoryPass` | fold `(base, offset)` to one flat address, then split wide cells into bytes; both no-ops unless their `--memory-model` is selected |
| final | `UnusedVarPass`, `EmptyEdgeRemovalPass`, `UnusedLocRemovalPass` | drop what the instrumentation made dead |

Passes not in this pipeline are used by individual backends: `MutexToVarPass`,
`AssumeFalseRemovalPass`, `AtomicReadsOneWritePass` and `WitnessOptimizer` by the OC checker,
`SsaPass`/`NoUninitVar`/`HavocToUninitVar` by the monolithic and Horn adapters, and
`DereferenceToArrayPass` by the backends that want memory as arrays rather than as dereferences.

## Rules the passes follow

- **Consumers before generic havoc.** Every pass that understands a specific call (`malloc`, `free`,
  `pthread_*`, nondet, `mem*`, the stdio/string stubs) runs before `UnresolvedInvokeToHavocPass`. A
  call nothing consumed reaches the analysis as a procedure that does not exist and fails there with
  "No such method ...".
- **Copies before havocs.** `MemoryFunctionsPass` spells out `memcpy`/`memset` before anything havocs
  the same objects: a havoc would leave the destination holding what it held before, which is not
  what a copy does.
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
