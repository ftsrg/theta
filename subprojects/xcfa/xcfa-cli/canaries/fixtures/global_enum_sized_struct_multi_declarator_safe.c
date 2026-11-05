// Each declarator of such a declaration keeps its own initializer.
extern void reach_error(void);
enum { N = 4 };
typedef struct { int e[N]; long mask; } Q;
Q a, b = { .mask = 3 };
int main(void) { if (a.mask != 0 || b.mask != 3) reach_error(); return 0; }
