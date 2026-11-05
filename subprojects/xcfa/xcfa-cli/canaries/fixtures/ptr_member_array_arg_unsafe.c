extern void reach_error(void);
extern int __VERIFIER_nondet_int(void);
typedef struct { int v; } C;
typedef struct { C q[2]; C g; int h; } L;
void w(C *c, int x){ c->v = x; }
L l;
void init(L *p, int i){ w(&p->q[i], 5); }
int main(void){ int i=__VERIFIER_nondet_int(); if(i<0||i>1) return 0; l.q[0].v=0; l.q[1].v=0; init(&l,i); if(l.q[i].v== 5) reach_error(); return 0; }
