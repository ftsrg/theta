extern void reach_error(void);
typedef struct { int v; int w; } C;
C a[3];
void g(C *c){ c++; c->w=5; }
int main(void){ a[1].w=0; g(&a[0]); if(a[1].w== 5) reach_error(); return 0; }
