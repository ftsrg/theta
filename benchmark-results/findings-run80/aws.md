# aws_* harness family — run 80 wrong results

STATUS: in progress. Bug A + Bug B confirmed (false-alarm subgroup). Negated-harness
subgroup (missed bugs) still under investigation.

## FAMILY / SIZE

11 wrong results, all under `/home/coder/sv-benchmarks/c/aws-c-common/`.
All tasks are `data_model: LP64`.

## SPLIT

### Subgroup 1 — FALSE ALARMS (theta says false, expected true): 3
| task | property | theta | expected |
|---|---|---|---|
| `aws_linked_list_init_harness.yml` | unreach-call | false(unreach-call) | true |
| `aws_string_compare_harness.yml` | unreach-call | false(unreach-call) | true |
| `aws_ring_buffer_acquire_harness.yml` | no-overflow | false(no-overflow) | true |

### Subgroup 2 — MISSED BUGS (theta says true, expected false): 8
All are `_negated` harnesses (unreach-call, expected verdict false):
`aws_byte_buf_init_copy_from_cursor_harness_negated`,
`aws_byte_buf_init_copy_harness_negated`,
`aws_byte_buf_init_harness_negated`,
`aws_byte_cursor_read_be16_harness_negated`,
`aws_byte_cursor_read_be32_harness_negated`,
`aws_byte_cursor_read_be64_harness_negated`,
`aws_byte_cursor_read_u8_harness_negated`,
`aws_string_new_from_array_harness_negated`.

---

## CONFIRMED ROOT CAUSE — Bug B (the one that breaks `aws_linked_list_init_harness`)

**`&outer.member` for a struct-typed member yields the address of the parent's *slot*,
not the address of the sub-object that `outer.member.field` actually reads/writes.**

Theta models a nested struct member as a **separately allocated sub-object**, with the
parent's slot holding a *pointer* to it. But the `&` operator on such a member returns
`parent_address + member_index` (the slot address) instead of the pointer value stored in
that slot. Field access through the member (`o.x.a`) goes through the slot with a *double*
dereference, while `&o.x` produces a *single*-level address. The two disagree, so a
struct-member pointer and the member itself stop aliasing.

Present under **both** `--memory-model multi` and `--memory-model flat`.

### Evidence (serialized model, `--enable-c-serialization`)

Source `repB2.c`:
```c
struct node { int a; int b; };
struct outer { struct node x; struct node y; };
int main() {
    struct outer o;
    struct node *p = &o.x;
    p->a = 7;
    if (o.x.a != 7) reach_error();   // unreachable in C
    return 0;
}
```
Serialized model under `--memory-model flat`:
```
main__o = (65536 * (__malloc + 1));            // o  -> object address O
0[(+ main::o 0)] = (65536 * (__malloc + 1));   // *(O+0) = S_x   (o.x is a SEPARATE object at S_x)
0[(+ main::o 1)] = (65536 * (__malloc + 1));   // *(O+1) = S_y

main__p = main__o;                             // p = &o.x  ==>  O        <-- WRONG, must be *(O+0) = S_x
0[(+ main::p 0)] = 7;                          // p->a = 7  ==>  *(O+0) = 7   <-- clobbers the S_x pointer

// o.x.a  ==>  0[(+ (deref 0 (+ main::o 0) Int) 0)]  ==  *( *(O+0) + 0 )  ==  *(7+0)
```
`&o.x` evaluates to `O`, but `o.x.a` is `*(*(O+0)+0)`. The store through `p` overwrites the
sub-object *pointer* with the value 7, and the read-back then dereferences address 7.
Native gcc: no error (safe). Theta: `(SafetyResult Unsafe Trace length: 3)`.

### Minimal repros (both false alarms; gcc-verified safe)
```c
// repB2.c — write through the member pointer, read via the member
struct node { int a; int b; };
struct outer { struct node x; struct node y; };
int main() { struct outer o; struct node *p = &o.x; p->a = 7;
             if (o.x.a != 7) reach_error(); return 0; }

// repB1.c — write via the member, read through the member pointer
struct node { struct node *next; struct node *prev; };
struct list { struct node head; struct node tail; };
int main() { struct list l; l.head.next = 0; l.head.prev = 0;
             struct node *p = &l.head;
             if (p->next != 0) reach_error(); return 0; }
```
Verdicts (PRED_CART, LP64):

| repro | multi | flat | native |
|---|---|---|---|
| repB1 | Unsafe | Unsafe | safe |
| repB2 | Unsafe | Unsafe | safe |
| rep3 (`o.x.a=7` first, then `p=&o.x; p->a`) | Safe | Unsafe | safe |

(`rep3` passing under `multi` is incidental — different statement order lets constant
folding hide it; flat exposes it.)

### Why this explains `aws_linked_list_init_harness`

`aws_linked_list_init_harness.i` is:
```c
struct aws_linked_list list;            // { struct aws_linked_list_node head, tail; }
aws_linked_list_init(&list);            // head.next=&tail; head.prev=0; tail.prev=&head; tail.next=0;
__VERIFIER_assert(aws_linked_list_is_valid(&list));
```
`aws_linked_list_is_valid` calls `aws_linked_list_is_valid_deep`, which does
`temp = &list->head;` and then `aws_linked_list_node_next_is_valid(temp)` = `node->next &&
node->next->prev == node`.

In the serialized model (the harness is auto-downgraded to `flat`; see the note
`frontend build failed due to a pointer-splitting limitation under --memory-model multi;
retrying with --memory-model flat`):
- `list->head.next = &list->tail`  →  `*( *(list+0) + 0 ) = list + 1`
  (double deref on the lhs; `&list->tail` is the slot address `list+1`)
- `temp = &list->head`             →  `temp = list`   (single-level slot address)
- `temp->next`                     →  `*(list + 0)`   = the *head sub-object pointer*, not `head.next`
- `temp->next->prev`               →  `*(headobj + 1)` = `head.prev` = 0
- `0 == temp` (`list`, nonzero)    →  false  →  `node_next_is_valid` = 0
  → `is_valid_deep` = 0 → `is_valid` = 0 → assert fails → `reach_error()`

Reproduced directly: `--backend CEGAR --domain PRED_CART` on the real task gives
`(SafetyResult Unsafe Trace length: 8)`, matching. (`--domain EXPL` gives
`NotSolvableException` instead.)

Also note `aws_linked_list_empty` (`list->head.next == &list->tail`) *passes* in the model —
both sides use the same wrong `&list->tail`, so the error only surfaces once the member
address is round-tripped through a pointer variable.

---

## CONFIRMED ROOT CAUSE — Bug A (`--memory-model multi` only)

**Storing an interior pointer (base + nonzero offset) into a memory cell emits two stores
to the *same* cell; the offset half clobbers the base half.**

`ReferenceElimination.changeComplexReferredVars`, `MemoryAssignStmt` branch
(`/home/coder/theta/subprojects/xcfa/xcfa/src/main/java/hu/bme/mit/theta/xcfa/passes/ReferenceElimination.kt`,
~lines 821-858) claims base and offset "go to two separate memory channels":
```kotlin
val baseDeref   = deref.replaceSplitRefs(splitVars, SplitChannel.BASE) ...
val offsetDeref = deref.replaceSplitRefs(splitVars, SplitChannel.OFFSET) ...
listOf(MemoryAssignStmt.create(baseDeref, baseExpr),
       MemoryAssignStmt.create(offsetDeref, offsetExpr))
```
But `replaceSplitRefs` only rewrites *split variables*. When the destination **address**
contains no split variable (the common case — writing into a struct field or an array
element), `baseDeref == offsetDeref`, so the two stores hit one cell. There is no distinct
offset shadow array; the "separate memory channel" does not exist.

### Evidence (serialized model)
`rep7.c` — nothing to do with nested structs, just an interior pointer:
```c
struct box { int *p; int *q; };
int main() { int arr[4]; struct box b; b.p = &arr[1];
             if (b.p != &arr[1]) reach_error(); return 0; }
```
Serialized under `multi`:
```
__theta_ref_tmp_0_base = main__arr;
main::b[0] = __theta_ref_tmp_0_base;   // store BASE  into b.p
main::b[0] = 1;                        // store OFFSET into b.p -- SAME CELL, clobbers base
 goto main_error;                       // comparison folded to "unequal"
```
Native: safe. Theta `multi`: `Unsafe`. Theta `flat`: **Safe** (flat keeps a pointer as one
scalar, so no split, no duplication — matches the design note at lines 131-139 of the file).

### Scope of Bug A (differential probes, all gcc-verified safe)
| repro | what it does | multi | flat |
|---|---|---|---|
| `rep2` | `l.head.next = &l.tail;` then compare | **Unsafe** | Safe |
| `rep7` | `b.p = &arr[1];` then compare | **Unsafe** | Safe |
| `rep9` | `*pp = &l.tail;` then compare via `slot` | **Unsafe** | Safe |
| `rep4` | `a.next = &b;` (whole-object address, offset 0) | Safe | — |
| `rep5` | `a.self = &a;` (self pointer, offset 0) | Safe | — |
| `rep6` | `q = &l.tail;` into a **local variable** | Safe | — |
| `rep8` | `g = &l.tail;` into a **global variable** | Safe | — |

Conclusion: plain variables are fine (they get a real `_base`/`_offset` var pair). Only
*memory cells* lose the offset, because a cell cannot hold two halves.

### Practical impact of Bug A on this family
Lower than Bug B: `aws_linked_list_init_harness` never reaches the `multi` build (the
pointer-splitting limitation throws first and the CLI silently retries with `flat`). Bug A
matters for any aws harness that *does* build under `multi` and stores an interior pointer.

---

## SUGGESTED FIXES (not implemented)

### Bug B (higher priority for this family)
File: the C frontend's address-of handling for aggregate members, plus
`ReferenceElimination` / the sub-object allocation that emits
`0[(+ parent i)] = <new sub-object address>`. `&outer.member` where `member` has
struct/array type must evaluate to **the value stored in the parent's slot**
(`*(parent + i)`), not to `parent + i`, so it agrees with the double-deref used by
`outer.member.field`.

Alternative and probably more robust: stop allocating nested struct members as separate
objects and lay the parent out flat (one object, member offsets from `ObjectLayout`), so
`&outer.member == parent + byte_offset(member)` and field access is a single deref. That
is what the `AD7 object layout` work (see MEMORY.md) was heading toward.

Risk: the sub-object-pointer representation is load-bearing for every struct access in the
frontend; changing `&` alone (option 1) is small but must also cover nested arrays,
`&outer.member.sub`, casts of the member pointer, and passing the member pointer to a
callee. Changing the layout (option 2) is a large, cross-cutting change that will move many
verdicts in both directions.

### Bug A
File: `/home/coder/theta/subprojects/xcfa/xcfa/src/main/java/hu/bme/mit/theta/xcfa/passes/ReferenceElimination.kt`,
`changeComplexReferredVars`, `MemoryAssignStmt` branch.
The two-store scheme needs a genuinely distinct offset channel (a shadow memory array
indexed by the same address), or interior pointers must be flattened to a single scalar
`base + offset` before the store (which is exactly what the flat model does).
Risk: a shadow channel has to be threaded through every load too (and through the OC /
data-race machinery); flattening on store loses the base/offset provenance that the
memsafety checks rely on. Simplest de-risked option: make the pointer-splitting limitation
detector also fire for "interior pointer stored into a memory cell" so those programs get
the `flat` retry (which is already correct here) instead of a silently wrong model.

---

## NOT YET DETERMINED
- Cause for the 8 `_negated` harnesses (missed bugs) — in progress.
- Cause for `aws_string_compare_harness` (false alarm) — not yet checked whether it is
  Bug B or something else.
- Cause for `aws_ring_buffer_acquire_harness` (no-overflow false alarm) — not yet checked.
