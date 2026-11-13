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
| | `PthreadArrayHandleUnrollPass` | unroll `for (i…) pthread_create(&t[i], …)` (or `t + i`) so the handle index is a constant | **before `CLibraryFunctionsPass`**, in a phase of its own: that pass keeps thread ids in the handles of the whole program as soon as one handle index stays non-constant, so it must see every procedure unrolled. **Before `ReferenceElimination`**, which folds `&t[i]` away. There is no `SimplifyExprsPass` this early, which is why it substitutes the loop variable itself. Letting simplification do it instead has no valid pass order: simplification must follow `ReferenceElimination` (or it folds an object's naming variable into its base id and later passes stop recognising the object), `ReferenceElimination` must follow the three passes that read `&x` as a reference, and `CLibraryFunctionsPass` cannot follow it at all because an address-taken local is re-based onto a runtime counter, leaving a thread handle with no static identity |
| | `CLibraryFunctionsPass`, `AtomicFunctionsPass` | model the pthread and `_Atomic`/`__atomic_*` families as XCFA labels (with a handle that has no static identity, every `pthread_create` writes a fresh thread id into its handle and every `pthread_join` waits for the exit flag of the id its handle holds; not for termination), and `strcpy`, `strlen` and `atoi`/`atol`/`atoll` exactly (`strlen` and `atoi` not for termination, nor when a stub writes a buffer inexactly, which leaves stale cells) | before `ReferenceElimination`: they read `&x` arguments as references |
| | `PthreadBarrierPass` | model `pthread_barrier_*` as blocking steps on per-barrier atomic globals | before `ReferenceElimination`: a barrier is identified by its `&barrier` argument |
| | `LibraryStubsPass` | model the stdio/string calls nothing defines, and record each over-approximated value (see the rules below) | **before `ReferenceElimination`**: a written pointer argument must still be `&x`, because a folded base id no longer carries its pointee type and the stub would then silently write nothing. **Before the instrumentation phase**, or the writes it does emit are never checked for races or memory safety. After `CLibraryFunctionsPass`, which flags the calls it handles itself |
| memory | `ReferenceElimination` | give every address-taken object a base id, turning `&x` into a pointer value and `*p` into a dereference; under memory safety, lower the lifetime-start markers and release locals at procedure exit | after every pass that needs to see a reference (all of group 1) |
| | `CallocFunctionPass` | lower `calloc` to `malloc` + a `memset` skipped when the block is NULL | before `MallocFunctionPass` and `MemoryFunctionsPass`, which model the two halves |
| | `MallocFunctionPass`, `AllocaFunctionPass` | turn allocation calls into assignments out of the shared base counter; `malloc`/`realloc` may also return NULL, `alloca` never does | after the frontend published its static-base high-water mark, so the counter is seeded past it |
| optimizing | `SimplifyExprsPass`, `UnrollPass`, `EmptyEdgeRemovalPass` | constant-fold, then unroll loops (and expand recursion, when a recursion bound is set) | `UnrollPass` needs **a `SimplifyExprsPass` after it** (the one in the cleanup phase) to fold the loop variable into the copies it made |
| calls | `FunctionPointerCallsPass` | expand a call through a function pointer into a dispatch over its candidates | before `InlineProceduresPass`, so the direct calls it produces can be inlined |
| | `InlineProceduresPass`, `NondetFunctionPass`, `InlinedProcedureRemovalPass` | inline what can be inlined (in a procedure that cannot be inlined, convert each call's arguments to the parameters' C types instead), model `__VERIFIER_nondet_*`, drop the bodies left behind | removal after inlining |
| | `ThreadResultPass` | start a copy of each routine whose result `pthread_join` reads, which stores its return value under the result id `CLibraryFunctionsPass` passes it (and sets the exit flag of that id, when handles hold thread ids) | after inlining, so the copy is of the finished body; in its own phase, as it adds procedures; before `CloneProcedureForStaticThreadsPass`, which may specialize the copies |
| | `ThreadLocalVarPass` | give each thread a local copy of a `__thread` global | after inlining, so a call left over can be refused; before the second `ReferenceElimination`, which then places an address-taken copy per thread |
| | `ReferenceElimination` (again) | inlining binds `&…` arguments to parameters only now, and no reference may reach the analyses | after `InlineProceduresPass` |
| cleanup | `PrintfReturnBoundPass` | bound the return of a stubbed `*printf` call by the longest text of its format literals | after inlining, which assigns each format argument its literal; before `StringLiteralInitPass`, which can drop the literal's initialization |
| | `FormatAccessPass` | under memory safety, turn the markers of a stubbed formatted call into the string reads and writes its format implies | after inlining, for the same reason as `PrintfReturnBoundPass`; before `MemoryFunctionsPass`, which lowers those reads and writes |
| | `EmptyEdgeRemovalPass`, `SimplifyExprsPass`, `UnusedLocRemovalPass`, `RemoveDeadEnds`, `EliminateSelfLoops`, `StaticCoiPass` | shrink the CFA before the instrumentation below multiplies it | `StaticCoiPass` after inlining; `SimplifyExprsPass` is also what folds `UnrollPass`'s copies |
| instrumentation | `MemoryFunctionsPass` | spell out `memcpy`/`memset`/`memmove` over the destination's cells, as a loop for a symbolic length (`memmove` copies down when the destination is after the source) | **before `MemsafetyPass`**, which guards its accesses, and before anything that havocs the same objects, i.e. before `UnresolvedInvokeToHavocPass` |
| | `NarrowCellRangePass` | constrain a narrow cell's value to what its C type can hold | before `MemsafetyPass` and `OverflowDetectionPass`, which read those cells |
| | `MemsafetyPass`, `NoSideEffectPass`, `HavocPromotionAndRange` | build the memory-safety guards (or, for other properties, end the path at a NULL dereference; an entry point that reads its pointer parameter `argv` is refused, as nothing allocates what it points to) and clean up what they leave | after every pass that creates a dereference to guard |
| | `LbePass` (+ `NormalizePass`, `DeterministicPass`) | large-block encoding | re-normalize after it: it re-shapes labels |
| | the witness pass, if a witness is being applied or validated | | after `LbePass`'s re-normalization |
| | `DataRaceToReachabilityPass`, `OverflowDetectionPass` | reduce the data-race and overflow properties to reachability. `OverflowDetectionPass` also leads a signed overflow to an undefined-behavior location when a termination witness is validated | **after every pass that creates a memory access**, or that access is not instrumented and the property is silently under-checked |
| | `UnresolvedInvokeToHavocPass` | havoc whatever calls are left, except those a havoc misrepresents (`fork`, exit handler registration, unmodeled synchronization, pointer-writing calls), which fail loudly | **last** of the call-consuming passes, by definition |
| | `AmbiguousMutexPass` | collect guarded literal-address alternatives across the whole XCFA; if any mutex or attribute address remains unresolved, invoke `SymbolicMutexPass` to replace ordinary mutexes with shared ownership arrays and ghost thread IDs | resolve all procedures before applying any alternatives, so symbolic and literal aliases share the same encoding |
| memory model | `FlatMemoryPass`, `ByteMemoryPass` | fold `(base, offset)` to one flat address, then split wide cells into bytes and keep a `_Bool` in its byte; both no-ops unless their `--memory-model` is selected | after every pass that creates or rewrites a dereference; `ByteMemoryPass` after `FlatMemoryPass` |
| final | `UnusedVarPass`, `EmptyEdgeRemovalPass`, `UnusedLocRemovalPass` | drop what the instrumentation made dead, and the writes to global objects that nothing reads (a union only as a whole) | last |
| | `DataRaceToReachabilityPass` | the portfolio's form of the data-race reduction, on the finished XCFA | after the `mem*` calls are spelled out and unresolved calls havoced |
| | `PtrSizeToMemoryPass` | with `--ptr-size-in-memory` (OC only), move the memory-safety ghost arrays into memory, and their constant static entries into tables in the reads; under flat with the OC backend, also the mutex ownership arrays of `SymbolicMutexPass` | last: anything before it may still rewrite dereferences |

Passes not in this pipeline are used by individual backends: `MutexToVarPass`,
`AssumeFalseRemovalPass`, `AtomicReadsOneWritePass`, `AllocationSitesPass` and `WitnessOptimizer` by
the OC checker, `NoUninitVar`/`HavocToUninitVar` by the Horn checker, and `DereferenceToArrayPass`
by the backends that want memory as arrays rather than as dereferences.

## Packages

The passes are grouped by what they are about, not by pipeline phase. The pass infrastructure
(`ProcedurePass`, `ProcedurePassManager` with `CPasses` and the other managers) and the shared
helpers in `Utils.kt` stay in this package.

| package | contents |
|---|---|
| `structure` | the shape of the CFA: normal form, determinism, removal of dead edges, locations and variables, large-block encoding, expression simplification, cone of influence, havoc/uninit conversions |
| `procedures` | calls: inlining, function pointers, the call graph, and calls left unresolved or ignored |
| `loops` | unrolling and its cut points, spin-loop detection |
| `library` | the C library and the verifier intrinsics: `CLibraryFunctionsPass` (pthread and string calls), stubs, math functions, `__VERIFIER_*`, string literals and formatted I/O, `mem*` |
| `memory` | references, allocation, the memory models (`flat`, `bytes`, arrays) and memory-related bounds |
| `concurrency` | threads, mutexes, barriers, atomics and thread-local storage |
| `property` | error and final locations and the reductions of memory safety, overflow and data races |
| `witness` | applying an input witness |

Witness application and termination-witness passes need `:theta-c2xcfa` and therefore live in
`:theta-xcfa-cli`; `BlockEncoding`'s passes are part of that encoding in `:theta-xcfa-analysis`.

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
- **An over-approximated value is recorded.** It is safe for a Safe verdict only: a
  counterexample that needs it may not exist in C. A pass that havocs a value which C computes (a
  stub's result, a formatted buffer) adds the variable to `XcfaBuilder.overApproximatedVars`, with
  the interval of its C type. Values from the environment (input, `rand`) are not recorded. xcfa-cli
  turns an Unsafe result into Unknown if its counterexample depends on a recorded value. An exact
  environment model records nothing: `fgets`, `read`/`recv` and the `scanf` family write every
  cell C may write (a `scanf` string, and a character buffer of a size that is not a small
  constant, only its first, but the memory-safety guards check the last one it may reach), and the
  socket calls return only the values POSIX allows.
- **Refuse loudly rather than model approximately.** A tool error scores nothing under SV-COMP; a
  wrong answer scores much worse. A pass that cannot state a construct exactly declines it, and logs
  why -- the call is then left in place and surfaces later as "No such method ...". When the bytes
  model could state it, the pass throws `RequiresByteAddressedMemoryException` instead, and the
  frontend is rebuilt under `--memory-model bytes`.
- **A pass leaves the builder consistent.** Every edge must run between two locations the procedure
  still lists; `ProcedurePass.runChecked` asserts this after each pass, so run passes through it.

See also [`c2xcfa`](../../../../../../../../../../c2xcfa/README.md) for how objects, cells and the
memory models are represented, which several of these passes depend on.
