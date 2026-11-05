extern void reach_error(void);
extern int __VERIFIER_nondet_int(void);
int x[2]; int y[2]; int *g=x;
void w(int *c){ *c=5; }
int main(void){ int **pp=&g; int i=__VERIFIER_nondet_int(); if(i<0||i>1) return 0; x[0]=0;x[1]=0; w(*pp+i); if(x[i]==5) reach_error(); return 0; }
