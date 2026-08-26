// batch 39: __typeof__(type-name) resolves to the named type
extern __typeof__(unsigned long) g;
int main() { __typeof__(int) x = 3; return x != 3; }
