void reach_error(void) {}
long g(char *p, unsigned char k) { if (p != 0) reach_error(); return 300 + k; }
int main() { long (*f)(char*, unsigned char) = g; long r = f(0, 255); if (r != 555) reach_error(); return 0; }
