// batch 40: C11 anonymous union member flattened through member lookup
struct S { union { int a; int b; }; int c; };
int main() { struct S s; s.a = 1; s.c = 2; return (s.a != 1) + (s.c != 2); }
