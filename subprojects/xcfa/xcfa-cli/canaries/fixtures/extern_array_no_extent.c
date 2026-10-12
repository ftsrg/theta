// `extern T a[];` at file scope is a *declaration*, not a definition: with `extern` and no
// initializer it is not even a tentative definition (C17 6.9.2p2), and an array type written
// without a size is incomplete (6.7.6.2p4). The extent is fixed by the definition, which lives in
// another translation unit and is not part of the task -- so here it is not merely missing, it is
// unknowable. None of the uses C permits on an incomplete array needs it either: `&a`, `a` decaying
// to `T *`, and `a[i]` all need only the element type, and `sizeof a` (which would) is a constraint
// violation a compiler rejects.
//
// The frontend demanded one anyway -- "Array with unspecified size must have initializer list" --
// and refused the whole file. The shape is everywhere in LDV sources:
// `extern unsigned char const _ctype[];`, `extern u32 const cx88_user_ctrls[];`,
// `extern struct device_attribute *ata_common_sdev_attrs[];`.
//
// Checked as valid-memsafety on purpose, because the extent is also what `__theta_ptr_size` records
// for the object, and any *invented* extent is a wrong `false(valid-deref)` waiting to happen: the
// real `_ctype` has 256 entries and is indexed by a whole `char`, so an object modelled as one
// element would report the very first `ctype_table[c]` below as an invalid dereference. An object
// this translation unit does not define is one it cannot bound.
extern void abort(void);
void reach_error() { abort(); }
extern unsigned char __VERIFIER_nondet_uchar(void);

/* declared here, defined elsewhere -- exactly as the LDV files have them */
extern unsigned char const ctype_table[];
extern int const *pointer_table[];

int main() {
  unsigned char c = __VERIFIER_nondet_uchar();

  /* indexing an object of unknown extent is legal C at any index this file can produce, and must
     not be reported as an invalid dereference */
  unsigned char flags = ctype_table[c];

  /* the cells are storage, not a fresh unknown per read: the same index reads back the same value */
  if (ctype_table[c] != flags) reach_error();

  /* decay to a pointer -- what most of the LDV files do with these arrays, and all they do with
     the pointer-element ones */
  unsigned char const *p = ctype_table;
  if (p == 0) reach_error();

  int const *q = pointer_table[3];
  if (q != pointer_table[3]) reach_error();

  return 0;
}
