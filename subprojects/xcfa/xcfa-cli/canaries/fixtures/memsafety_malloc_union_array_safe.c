// An element of a malloc'd array of unions is in bounds.
extern void reach_error(void);
extern void *malloc(unsigned long);
extern void free(void *);
union U { int a; char b[4]; };
int main(void) { union U *p = malloc(2 * sizeof(union U)); if (!p) return 0; p[1].b[3] = 1; free(p); return 0; }
