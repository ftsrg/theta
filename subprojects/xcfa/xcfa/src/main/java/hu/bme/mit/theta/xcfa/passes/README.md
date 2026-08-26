# XCFA procedure passes

Passes rewrite a procedure after it is built and before an analysis sees it. `ProcedurePassManager`
fixes the order, and **the order is part of the contract** — several passes are only correct in a
particular position. The comments there give the reason for each group; the recurring ones:

- **Consumers before generic havoc.** Every pass that understands a specific call (`malloc`, `free`,
  `pthread_*`, nondet, `mem*`, the stdio/string stubs) runs before `UnresolvedInvokeToHavocPass`.
  A call nothing consumed reaches the analysis as a procedure that does not exist and fails there
  with "No such method ...".
- **Copies before havocs.** `MemoryFunctionsPass` spells out `memcpy`/`memset` before anything havocs
  the same objects: a havoc would leave the destination holding what it held before, which is not
  what a copy does.
- **`LoopUnrollPass` runs early**, so a loop a later pass *emits* (a symbolic-length fill, a
  nondet fill over a large region) is never unrolled and reaches the analyses as a real loop. That is
  deliberate: unrolling those is not a better answer but no answer at all.
- **The memory-model passes run last.** `FlatMemoryPass` folds `(base, offset)` to one flat address
  downstream of everything that creates or rewrites a dereference; `ByteMemoryPass` then splits wide
  dereferences into byte cells. Both are no-ops unless their model is selected.
- **Range constraints before the guards that read them**, so a memsafety or overflow guard sees a
  `char` cell that can only hold `char` values.

## Modelling rules

- **A havoc is bounded to the C type it writes.** A bare havoc is unconstrained across its whole SMT
  sort — under integer arithmetic that is the *unbounded* integers — so an unbounded havoc can hand
  back a value no object of that type could hold. Every stub havoc carries the same bound a
  `__VERIFIER_nondet_<type>()` result does.
- **Havoc rather than leave stale.** Where a write is only partly modelled (a straddled tail cell, a
  region a stub writes through a pointer), the affected cells are havoc'd. Unconstrained is a safe
  over-approximation; the old value is one specific wrong value that can hide a bug as easily as
  invent one.
- **Refuse loudly rather than model approximately.** A tool error scores nothing under SV-COMP; a
  wrong answer scores much worse. A pass that cannot state a construct exactly should decline it and
  say why. Note that a *declined* call is left in place and surfaces later as "No such method ...",
  so declining is not silent — but it is also not a diagnosis, which is why the decline sites log.

See also [`c2xcfa`](../../../../../../../../../../c2xcfa/README.md) for how objects, cells and the memory
models are represented, which several of these passes depend on.
