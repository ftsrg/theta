// Assigning one union to another. Ordinary C, and the intel-tdx sources are full of it:
// `lookup_context->field_id = tdvps_lookup[i].field_id;` where the type is a uint64 overlaid with
// a bitfield struct.
//
// It was refused as "Could not handle left-hand side of assignment: lhs is a BvAddExpr". Nothing
// was misparsed -- an aggregate's value in theta IS its base address, so an aggregate lvalue
// arrives as `base + offset` instead of as a dereference. The copy path then rejected it because
// unions were excluded outright: a struct copies member by member, but a union's members alias one
// region, so member-wise copying would write the same storage repeatedly through different views.
//
// The fix re-initialises the destination's STORAGE from the source's -- the same cells
// ExpressionVisitor reads members out of. This fixture checks that the copy is real (the value
// arrives) and that it is a copy (later writes to the source do not follow), through BOTH views of
// the union, which is what a member-wise copy would get wrong.
extern void abort(void);
void reach_error() { abort(); }

typedef union {
  unsigned int raw;
  struct { unsigned int lo : 16, hi : 16; } parts;
} id_t;

typedef struct { id_t id; unsigned int tag; } holder_t;

int main() {
  holder_t h;
  id_t src;

  src.raw = 0xDEADBEEFu;
  h.id = src;                                   /* union assignment through a struct member */
  if (h.id.raw != 0xDEADBEEFu) reach_error();   /* arrived, read through the raw view */
  if (h.id.parts.lo != 0xBEEFu) reach_error();  /* and through the bitfield view */
  if (h.id.parts.hi != 0xDEADu) reach_error();

  src.raw = 0u;                                 /* it is a copy, not an alias */
  if (h.id.raw != 0xDEADBEEFu) reach_error();

  h.tag = 5u;                                   /* the copy did not spill into the sibling member */
  if (h.id.raw != 0xDEADBEEFu) reach_error();
  if (h.tag != 5u) reach_error();
  return 0;
}
