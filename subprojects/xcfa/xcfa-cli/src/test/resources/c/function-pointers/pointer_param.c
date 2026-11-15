void reach_error(void) {}
long g(char *p) { reach_error(); return 0; }
int main() { long (*f)(char*) = g; f(0); return 0; }
