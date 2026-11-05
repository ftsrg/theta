extern void reach_error(void);
extern int __VERIFIER_nondet_int(void);
int a[3];
void r(int *p,int n){ if(n==0){ *p=5; return; } r(&a[n-1],n-1); }
int main(void){ a[0]=0; r(&a[2],2); if(a[0]!=5) reach_error(); return 0; }
