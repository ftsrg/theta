typedef unsigned int u32;
typedef union { float value; u32 word; } shape;
int main() { shape u; u.value = 1.0f; return u.word; }
