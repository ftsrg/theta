// batch 39: __builtin_offsetof
struct S { int a; int b; int c; };
int main() { unsigned long o = __builtin_offsetof(struct S, c); return o == 0; }
