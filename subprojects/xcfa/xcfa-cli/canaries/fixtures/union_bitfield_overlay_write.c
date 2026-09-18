// writing a bitfield of a union's packed-struct view.
//
// `u.parts.f = v` read-modify-writes the union's shared cell. The cell expression is stamped
// with the *struct's* C type -- that is what lets `.f` resolve as a field at all -- and every
// aggregate type reports the same pointer-width placeholder as its SMT sort, so the assignment
// cast the right-hand side to 64 bits and handed it to a 32-bit cell:
// "Expected type (Bv 32) but the expression has type (Bv 64)".
// `mktme_key_program.keyid_ctrl.command = 1` is the archetype.
// The splice must use the cell's own storage width, which is what this checks: the field write
// must land in exactly its own bits and leave the sibling integer view's other bits alone.
// Checked as PARSE-OK, not as a verdict, for a reason that is NOT about this fix: the bitfields
// make `efficient` resolve to bitvector arithmetic, and the STABLE portfolio's CEGAR then asks
// Z3-legacy to interpolate bitvectors, which it cannot do ("theory not supported by interpolation
// or bad proof"). That is a known, separate limitation -- bitvector + interpolation requires
// MathSAT. The values asserted below were validated against gcc (no reach_error is reached), and
// the sibling fixture union_wide_cell_halves.c does carry the semantic check as a real verdict.
// What this file guards is the part item 9 fixed: the frontend used to die building it with
// "Expected type (Bv 32) but the expression has type (Bv 64)", so it fails without the fix and
// parses with it.
extern void abort(void);
void reach_error() { abort(); }

typedef union {
  struct {
    unsigned int command : 8, enc_algo : 16, rsvd : 8;
  };
  unsigned int raw;
} ctrl_t;

ctrl_t g;

int main() {
  ctrl_t c;
  c.raw = 0u;
  c.command = 1u;
  if (c.raw != 1u) reach_error();
  c.enc_algo = 4u;
  if (c.raw != 1u + (4u << 8)) reach_error();
  c.rsvd = 0xABu;
  if (c.raw != 1u + (4u << 8) + (0xABu << 24)) reach_error();
  if (c.command != 1u || c.enc_algo != 4u || c.rsvd != 0xABu) reach_error();
  // the sibling view writes the whole word; the bitfield view must read it back
  c.raw = 0xDEADBEEFu;
  if (c.command != 0xEFu || c.enc_algo != 0xADBEu || c.rsvd != 0xDEu) reach_error();
  g.command = 2u;
  if (g.raw != 2u) reach_error();
  return 0;
}
