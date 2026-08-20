# Union byte layout (AD7, the intractable half) — design spec

## Why

`intel-tdx-module`: **836 runs, all ERROR in the frontend**. 596 of them die on
`Accessing member [X] of a union whose members do not all share a representation`;
the other 240 die earlier on `Referencing non-lvalue expressions is not allowed!`
(a different barrier, out of scope here).

The shapes are not single words — that is why batch 56's word-slicing cannot reach them:

```c
typedef union __attribute__((aligned(16))) {
    uint64_t qwords[2];
    uint32_t dwords[4];
    uint8_t  bytes[16];
} uint128_t;                       // 16 bytes

typedef union { uint64_t qwords[6]; uint8_t bytes[48]; } measurement_t;   // 48 bytes

typedef union ia32e_paging_table_u {
    ia32e_sept_t sept[512];
    ia32e_ept_t  ept[512];
} ia32e_paging_table_t;            // 4096 bytes
```

A 4 KB union has no word to slice. It needs genuine byte addressing.

## Key insight

Byte-granular *cells* turn variable-index punning into plain address arithmetic:
`u.dwords[i]` is bytes `[i*4, i*4+4)` — an arithmetic offset, **not** a variable bit-shift.
That matters because a variable bit-shift is expressible under bitvector but effectively
unusable under the integer encoding (it needs `2^(8i)`), and integer is the better default.
With byte cells, **both encodings work**: the recombination is `Concat` (bv) or
`sum cell[k+j] * 256^j` (int, linear — constant powers).

## Model

**Trigger.** A union is byte-laid-out iff it is a union whose members do not all share a
representation *and* `unionCellWidth() == null` (the existing "cannot be one sliced word"
signal). Word-sliceable unions keep the batch-56 path unchanged — this is purely additive.

**Storage.** The union owns a base id `u` and `sizeBits/8` cells, each one **byte**:
`arrays[u][0 .. size-1]`. Little-endian (x86; matches gcc, which `ObjectLayout` is validated against).

**Addressing.** From `ObjectLayout.of(union, arch)`: member `m` sits at
`byteOff = field.bitOffset()/8`, width `n = field.bitWidth()/8`. For an array member,
`u.m[i]` is at `byteOff + i * elementSizeBytes`.

**Read** of an n-byte member at byte offset `k`:
- bitvector: `Concat(cell[k+n-1], …, cell[k])`
- integer:  `sum_{j<n} cell[k+j] * 256^j`
then apply the member's signedness (sign-extend if signed).

**Write** of value `v` to an n-byte member at `k`: for `j in 0..n-1`
- bitvector: `cell[k+j] = Extract(v, 8j, 8j+8)`
- integer:  `cell[k+j] = (v / 256^j) mod 256`

No read-modify-write is needed for whole-byte members — each byte cell is written outright.

**Containment (the load-bearing decision).** A byte-laid-out union **always gets its own base
id**, so byte granularity never leaks into the surrounding object's element granularity. A
struct containing one stores the union's base id in that member's cell — exactly the existing
nested-aggregate mechanism ("an element containing a nested aggregate still needs one
allocation per element, written into the element's flat cell", batch 55).

## What must stay refused (fail loud, per project discipline)

- A member whose width is not a whole number of bytes (a bitfield inside a byte-laid-out union).
- Floating-point members — the batch-59 `fpToIEEEBV(NaN)` gate stands; do not reopen it here.
- Taking the address of a byte-laid-out member and doing pointer arithmetic that escapes the
  union (`&u.bytes[3]` flowing outward) — refuse initially rather than guess.

Refusing scores 0; guessing wrong scores −16. Keep the existing exception type and message style.

## Sites to change

1. `CStruct` / `ObjectLayout` — expose "is byte-laid-out" + byte offset/size per member.
2. `ExpressionVisitor` — `directMemberAccess` (and the ptr-member variant) must emit the
   multi-cell read for such unions; the array-subscript path must compute `byteOff + i*elemSize`.
3. `FrontendXcfaBuilder` — the assignment path must emit the multi-cell write; allocation must
   size the object in byte cells; initializers must fill byte cells.
4. Memsafety: `__theta_ptr_size` for these objects is in **byte** cells — must match, or bounds
   checks will false-alarm (this bit the VLA work before).

## Validation (non-negotiable)

- Module tests in **both** encodings (`integer` and `bitvector`) — every new test uses the
  both-encodings helper.
- Semantic, not structural: assert cross-view punning end to end, e.g.
  `u.qwords[0] = 0x0102030405060708; u.bytes[0] == 0x08 && u.bytes[7] == 0x01` proves Safe,
  and negating it proves Unsafe (so the check is not vacuous).
- A canary fixture per shape + the 255-canary parse suite + `run_fixtures.sh`.
- Guard the refusals with `assertThrows` so the boundary cannot silently widen.

## ROI caveat — state this plainly

Unlocking the frontend is **not** the same as gaining score. These TDX files are large: they
already burn 17–22 s of CPU *just failing in the frontend*. ERROR and TIMEOUT both score 0, so
if they unlock into timeouts the 596 tasks gain nothing. The batch-58 VLA experience is the
precedent: soundness restored, capability not gained. Expected verdicts are mostly `false`
(unreach-call), and finding a counterexample is usually cheaper than proving safety, so there
is a real chance of verdicts — but it is a chance, not a certainty. Measure on a sample of
~12 TDX files before committing to the full implementation.
