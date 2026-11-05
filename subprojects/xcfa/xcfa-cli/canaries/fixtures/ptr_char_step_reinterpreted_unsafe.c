extern void reach_error(void);
extern int __VERIFIER_nondet_int(void);
int a[3];
void w(int *c){ *c=5; }
int main(void){ a[1]=0; int *p=a; int *q; w((int*)((char*)p+4)); if(a[1]== 5) reach_error(); return 0; }
