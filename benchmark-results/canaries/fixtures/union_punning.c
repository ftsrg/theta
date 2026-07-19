// batch 43: union of pointer + pointer-wide unsigned must alias (sameRepresentation relaxation)
union U { void *ptr; unsigned long i; };
int main() {
  union U u; int x = 5;
  u.ptr = &x;
  if (u.i == 0) return 1;
  u.i = 0;
  if (u.ptr != 0) return 2;
  return 0;
}
