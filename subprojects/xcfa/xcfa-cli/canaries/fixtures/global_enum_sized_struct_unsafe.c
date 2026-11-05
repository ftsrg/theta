// A global of a struct typedef with an enum-sized array member keeps its declaration.
extern void reach_error(void);
enum { N = 4 };
typedef struct { int e[N]; long mask; } Q;
Q q;
int main(void) { q.mask = 1; if (q.mask == 1) reach_error(); return 0; }
