// Stepping a pointer to a union reaches the next element of a declared array.
extern void reach_error(void);
extern void *malloc(unsigned long);
extern void free(void *);
union U { int a; char b[4]; };
union U g[2];
int main(void) { g[1].a = 7; union U *p = g; p++; if (p->a != 7) reach_error(); return 0; }
