// batch 39: __builtin_types_compatible_p over type names
int main() { int a = __builtin_types_compatible_p(int, int); int b = __builtin_types_compatible_p(int, long); return a + b; }
