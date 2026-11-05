// An access past a malloc'd union is an overrun.
extern void reach_error(void);
extern void *malloc(unsigned long);
extern void free(void *);
union U { int a; char b[4]; };
int main(void) { union U *p = malloc(sizeof(union U)); if (!p) return 0; p->b[5] = 1; free(p); return 0; }
