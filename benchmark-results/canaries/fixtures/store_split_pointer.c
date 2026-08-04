// A pointer value occupies exactly one memory cell, so it must be stored as one value --
// and a base/offset pair is two. `ReferenceElimination` used to emit two MemoryAssignStmts,
// one per "channel", but there is no second channel: `multi` has one memory array and one
// __theta_ptr_size. When the address is an ordinary cell -- the common `struct { T *p; }`
// field -- both dereferences are identical, so the second store clobbered the first and the
// cell was left holding the bare offset with the base lost. `ptr_size[1] == 0`, and the next
// read through it was reported as an invalid dereference (memsafety-ext3/test27-1 twice).
// Storing a mid-object pointer is now refused, which hands the program to --memory-model
// flat, where such a pointer is a single scalar address and needs no channels.
extern void abort(void);
void reach_error() { abort(); }

struct C {
  int *p;
};

int main(void) {
  int a[10];
  struct C c;
  a[1] = 42;
  c.p = &a[1];
  if (*(c.p) != 42) reach_error();
  *(c.p) = 7;
  if (a[1] != 7) reach_error(); // the stored pointer still names a[1], not some other object
  return 0;
}
