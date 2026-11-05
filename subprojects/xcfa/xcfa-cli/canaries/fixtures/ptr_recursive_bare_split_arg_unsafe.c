extern void reach_error(void);
extern int __VERIFIER_nondet_int(void);
int a[3];
void r(int *p,int n){ if(n==0){ *p=5; return; } int *q; q=&a[n-1]; r(q,n-1); }
int main(void){ a[0]=0; int *s; s=&a[2]; r(s,2); if(a[0]== 5) reach_error(); return 0; }
