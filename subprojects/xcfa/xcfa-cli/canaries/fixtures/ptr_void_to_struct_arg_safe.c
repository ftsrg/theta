extern void reach_error(void);
extern int __VERIFIER_nondet_int(void);
typedef struct { int pid; int id; int v; } T;
void set(void *p){ T *t = (T*)p; t->v = 7; }
int main(void){ T a[2]; a[0].v=0; a[1].v=0; int i=__VERIFIER_nondet_int(); if(i<0||i>1) return 0; set((void*)&a[i]); if(a[i].v!= 7) reach_error(); return 0; }
