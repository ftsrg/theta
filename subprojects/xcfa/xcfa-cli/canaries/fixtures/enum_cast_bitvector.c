// batch 42: an undeclared enum is an int, not CVoid (only crashes under bitvector arithmetic)
struct S { int arr[4]; enum unknown_tag e; };
struct S g;
int main() { g.e = 0; return g.arr[0]; }
