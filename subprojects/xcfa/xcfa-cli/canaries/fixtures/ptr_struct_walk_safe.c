extern void reach_error(void);
typedef struct { int k; int v; } T;
T t[4];
int main(void){ for(int i=0;i<4;i++){ t[i].k=i; t[i].v=0; } T *p; for(p=t;p<t+4;p++){ p->v=p->k+1; } if(t[3].v!= 4) reach_error(); return 0; }
