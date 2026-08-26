// A bitfield wider than one storage cell. The declared unit is assembled from several byte cells
// by concatenation, so a store has to splice the value across every cell the field overlaps and
// leave the rest alone. Before this worked, such an assignment died as "Could not handle left-hand
// side of assignment" -- the largest single after-parsing failure cause in the parse-only
// run (intel-tdx-module alone has 407 after-parsing files, whose fields are 52 bits over seven
// byte dereferences).
//
// The neighbour checks are the point. Concat's first operand holds the HIGH bits while addresses
// increase the other way, so a reversed mapping writes the right bits to the wrong bytes -- which
// a single-field round trip would happily pass. Writing one field and reading back the ones either
// side of it is what actually pins the order.
extern void abort(void);
void reach_error(){ abort(); }

struct wide {
  unsigned long long lo : 12;
  unsigned long long mid : 52;   /* spans several byte cells */
};

struct neighbours {
  unsigned long long a : 20;
  unsigned long long b : 24;
  unsigned long long c : 20;
};

int main() {
  struct wide w;
  w.lo = 0;
  w.mid = 0;

  /* a wide field round-trips its own value */
  w.mid = 0xABCDEF12345ULL;
  if (w.mid != 0xABCDEF12345ULL) reach_error();
  /*... and did not disturb its neighbour */
  if (w.lo != 0) reach_error();

  /* writing the narrow neighbour leaves the wide one intact */
  w.lo = 0xFFF;
  if (w.lo != 0xFFF) reach_error();
  if (w.mid != 0xABCDEF12345ULL) reach_error();

  /* three adjacent fields: each write must touch only its own bits */
  struct neighbours n;
  n.a = 0; n.b = 0; n.c = 0;
  n.b = 0xFFFFFF;
  if (n.a != 0) reach_error();
  if (n.c != 0) reach_error();
  if (n.b != 0xFFFFFF) reach_error();

  n.a = 0xABCDE;
  if (n.a != 0xABCDE) reach_error();
  if (n.b != 0xFFFFFF) reach_error();
  if (n.c != 0) reach_error();

  return 0;
}
