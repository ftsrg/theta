typedef unsigned long long u64;
typedef union { float value; u64 word; } shape;
int main() { shape u; u.value = 1.0f; return (int) u.word; }
