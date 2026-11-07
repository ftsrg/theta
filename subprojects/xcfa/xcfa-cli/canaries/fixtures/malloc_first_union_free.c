// The address of a heap struct's first member is the block's address, so freeing it is valid,
// also for a union member, which the flat model keeps as a separate object.
void *malloc(unsigned long);
void free(void *);
void abort(void);
struct s {
  union {
    int a;
    float b;
  } u;
  int x;
};

int main(void) {
  struct s *p = malloc(sizeof *p);
  if (!p) abort();
  p->u.a = 1;
  p->x = 2;
  free(&p->u);
  return 0;
}
