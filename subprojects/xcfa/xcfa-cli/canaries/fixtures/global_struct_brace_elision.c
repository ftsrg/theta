// `= { 0 }` over an ARRAY OF STRUCTS. C's brace elision (C17 6.7.10p17) gives the array a single
// initializer, so the first *element* -- a struct -- receives a bare scalar rather than its own
// brace list. That scalar initialises the element's first member, recursively its first scalar
// leaf, and every other member and element is zero.
//
// The frontend refused exactly that shape: "Unsupported initializer for global struct variable".
// It was the last remaining reported frontend error for the intel-tdx-module family,
// where `const fms_info_t disallowed_fms[6] = { 0 };` is the archetype.
//
// The zeroes matter as much as the parse: if the object were left unwritten its cells would be
// unconstrained, and a program reading them would get a spurious counterexample rather than the
// zeroes C guarantees a static object. So this is checked as a VERDICT, not as PARSE-OK.
extern void abort(void);
void reach_error() { abort(); }

typedef union {
  unsigned long long raw;
  struct { unsigned int lo; unsigned int hi; } parts;
} fms_t;

/* The archetype: `const fms_info_t disallowed_fms[6] = { 0 };` in the intel-tdx sources. The
   element type must be an aggregate for this to bite -- an array of plain structs was already
   accepted, so a struct-element version of this fixture does NOT discriminate. */
static const fms_t table[3] = { 0 };
static const fms_t seeded[2] = { { 0x00000002FFFFFFFDULL } };  /* element 0 set, element 1 zero */

int main() {
  /* unrolled on purpose: a canary must finish in seconds, and a loop over the array made the
     portfolio time out even though the file parses instantly. */
  if (table[0].raw != 0ULL) reach_error();
  if (table[2].raw != 0ULL) reach_error();
  if (table[1].parts.lo != 0u) reach_error();      /* zero through the other view too */

  if (seeded[0].raw != 0x00000002FFFFFFFDULL) reach_error();
  if (seeded[1].raw != 0ULL) reach_error();        /* the elided remainder really is zero */
  return 0;
}
