// Subscripting a pointer to a union still finds a reachable error.
extern void reach_error(void);
extern void* malloc(unsigned long);
extern void free(void*);
union U {
  int a;
  char b[4];
};
int main(void) {
  union U* p = malloc(2 * sizeof(union U));
  if (!p)
    return 0;
  p[1].a = 1;
  if (p[1].a == 1)
    reach_error();
  return 0;
}
