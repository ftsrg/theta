void reach_error(void) {}
void g(void) { reach_error(); }
int main() { void (*f)(void) = g; f(); return 0; }
