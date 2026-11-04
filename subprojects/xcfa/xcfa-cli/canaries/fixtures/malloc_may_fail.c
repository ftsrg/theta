// malloc may return NULL (C11 7.22.3), so the failure branch is reachable.
extern void abort(void);
void reach_error() { abort(); }
extern void *malloc(unsigned long);

int main() {
  int *p = (int *)malloc(sizeof(int));
  if (!p) reach_error();
  return 0;
}
