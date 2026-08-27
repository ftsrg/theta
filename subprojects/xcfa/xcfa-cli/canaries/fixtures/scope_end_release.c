// An object's storage dies when its *block* is left. Nothing said so:
// `__theta_ptr_size[base]` was written once at the allocation and cleared only by an
// explicit `free`, so a pointer to a block-local array stayed usable for the rest of the
// program (memsafety-ext3/scopes5 and scopes3, missed bugs).
extern void abort(void);
void reach_error() { abort(); }

int main() {
  int *p = 0;
  if (1) {
    int a[10];
    a[0] = 1;
    p = a;
  }
  p[0] = 2; // a is dead here
  return 0;
}
