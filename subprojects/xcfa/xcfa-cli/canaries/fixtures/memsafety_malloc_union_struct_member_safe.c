// A union's cell count is not one when a member spans several cells.
extern void reach_error(void);
extern void *malloc(unsigned long);
extern void free(void *);
struct R { int x; int y; int z; };
union U { int a; struct R r; };
int main(void) { union U *p = malloc(sizeof(union U)); if (!p) return 0; p->r.z = 1; free(p); return 0; }
