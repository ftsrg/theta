extern void reach_error(void);
int a[3];
void g(int *c){ c++; *c=5; c--; c+=2; *c=6; }
int main(void){ a[1]=0; a[2]=0; g(a); if(a[1]!= 5) reach_error(); if(a[2]!= 6) reach_error(); return 0; }
