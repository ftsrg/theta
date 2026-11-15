void reach_error(void) {}
unsigned char g(int x) { return (unsigned char)x; }
int main() { unsigned char (*f)(int) = g; unsigned char r = f(258); if (r != 2) reach_error(); return 0; }
