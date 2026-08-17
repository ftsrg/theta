// batch 39: GNU a ?: b (omitted middle operand)
int main() { int a = 3; int b = a ?: 7; int c = 0 ?: 9; return (b != 3) + (c != 9); }
