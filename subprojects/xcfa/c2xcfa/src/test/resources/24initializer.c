void reach_error(){}

int a;
int b = 1;
int c[10];
int d;
int e[] = {1,2,3};
struct S {
    int f;
    int g;
} s;
struct T {
    int h;
    struct S i;
} t;
int j[10][20];
struct U {
    int k;
    struct T l;
    int m[5];
    int* ptr;
} u;


int main() {
    if(a || b || c || d || e || s.f || t.i.g || j || u.ptr) reach_error();
}