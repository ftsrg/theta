extern void reach_error(void);
extern int __VERIFIER_nondet_int(void);
int a[3];
int main(void){ a[1]=0; void *v=a; v=v+4; int *q=(int*)v; *q=5; if(a[1]== 5) reach_error(); return 0; }
