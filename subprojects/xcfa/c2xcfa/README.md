# c2xcfa — building an XCFA from C

Turns the parsed C model (`c-frontend`) into an XCFA. Most of the difficulty is not control flow but
**how C objects are represented in memory**, which is what this document covers; it is the context
most of the surprising code here needs.

## Objects, cells and base ids

Memory is modelled as arrays indexed by an object identity and a position inside it, so every object
gets a **base id** and a run of **cells**.

- A cell is **one member or element**, whatever its C width. A struct of four `unsigned char` is four
  cells in four bytes, not one cell. Bitfields sharing a storage unit map to the **same** cell.
- **An aggregate's value IS its base address.** `&a`, `a` and `&a[0]` are the same expression, so a
  struct- or array-typed lvalue arrives as a base (or `base + offset`), never as a dereference of
  something else. Much of the assignment handling exists to tell that apart from a pointer value.
- A member that is itself an aggregate holds a **base id**, not contents. Copying that cell aliases
  the two objects instead of copying them, which is why whole-object copies are restricted to objects
  whose every cell is a scalar.
- `FrontendMetadata` is **identity-keyed**. A rebuilt expression is a different object and carries no
  `cType`, so any pass that reconstructs an lvalue loses its type unless it re-stamps it. Several
  recovery paths here exist only because of this; prefer re-stamping over re-deriving a type from an
  SMT sort, which cannot distinguish `struct S *` from `unsigned int`.

## Memory models

Selected with `--memory-model`; see `ArchitectureConfig.MemoryModelType`.

| model | pointer representation | notes |
|---|---|---|
| `multi` (default) | split into **base + offset**, memory is `arrays[base][offset]` | precise and cheap; cannot represent a pointer covering several cells, nor pointer arithmetic outside `pointer + integer` |
| `flat` | **one scalar address**, objects spaced `FLAT_STRIDE` apart | any pointer-arithmetic shape assigns directly |
| `bytes` | flat, but **every cell is one byte** | a wider read is a little-endian `Concat` of byte cells, a wider write an `Extract`-and-store; requires bitvector arithmetic |

Only `bytes` can express two differently typed views of the same storage (an `int` and the `char`s
overlapping it, a union member and its byte array), because there they are literally the same cells.

**Fallback chain.** The frontend builds under `multi`; a pointer-splitting failure rebuilds under
`flat`, and a construct needing byte granularity rebuilds under `bytes`. This applies only to the
*default* model — an explicit `--memory-model` is the caller's decision and is never overridden.

`bytes` **refuses floating-point objects**: SMT-LIB's FP sort has a single NaN, so an IEEE round trip
cannot preserve a payload, and not every solver implements `fp.to_ieee_bv` at all. A loud refusal is
deliberate — see the principle below.

## When in doubt, refuse

Under SV-COMP scoring a tool error is worth nothing and a wrong answer is worth substantially less
than nothing, so an unsupported construct must **fail loudly rather than be modelled approximately**.
Concretely: never leave a partially written object holding its old value (havoc it — unconstrained
over-approximates, a stale value is one specific wrong value), and never widen a type rule so far
that a derived type is indistinguishable from a declared one.
