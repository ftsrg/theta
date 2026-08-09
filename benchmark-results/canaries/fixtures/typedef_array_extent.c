// An array declared through a typedef used to lose its extent entirely: the variable was built as
// a scalar, no `alloca` was emitted for it, and so the object had no size -- the very first element
// read was then reported as an invalid dereference. Dimensions live on the *declarator*, and a
// typedef's brackets belong to the typedef's own declarator, not to the `arr_t a;` that uses it.
//
// This is what made the run-86 `memsafety/test-021x` and `list-ext-properties` family answer
// `false(valid-deref)` on programs that are safe -- they all declare their list as
// `typedef ... list_t[2]; list_t list;`. Those tasks had only just started answering at all
// (the frontend previously refused them), so the bug turned 0-scoring errors into wrong answers.
//
// The multi-dimensional case pins the dimension ORDER, which is the easy thing to get backwards:
// `typedef int A[2]; A x[3];` is `int[3][2]` -- the declarator's [3] is outermost. Reversed, the
// object still has the right total size and every single-dimension check would still pass, so only
// a row-size comparison catches it.
extern void abort(void);
void reach_error(){ abort(); }

typedef int arr_t[2];
typedef void *ptr_arr_t[2];

arr_t global_ints;              /* global, scalar elements */
ptr_arr_t global_ptrs;          /* global, pointer elements */

int main() {
  /* reading an element of a typedef'd array is a valid dereference */
  int a = global_ints[0];
  int b = global_ints[1];
  void *p = global_ptrs[0];
  if (a != 0) return 1;
  if (b != 0) return 2;
  if (p != 0) return 3;

  /* the same, for a local */
  arr_t local;
  local[0] = 5;
  local[1] = 6;
  if (local[0] + local[1] != 11) reach_error();

  /* writing through the whole extent stays in bounds */
  for (int i = 0; i < 2; i++) local[i] = i;
  if (local[1] != 1) reach_error();

  /* dimension order: A x[3] is int[3][2], so a row is 2 ints wide */
  arr_t x[3];
  int plain[3][2];
  if (sizeof(x) != sizeof(plain)) reach_error();
  if (sizeof(x[0]) != sizeof(plain[0])) reach_error();
  x[2][1] = 7;
  x[0][0] = 8;
  if (x[2][1] != 7) reach_error();
  if (x[0][0] != 8) reach_error();

  return 0;
}
