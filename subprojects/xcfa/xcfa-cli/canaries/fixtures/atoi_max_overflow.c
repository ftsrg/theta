// atoi("2147483647") is INT_MAX.
extern int atoi(const char *s);

int main() {
  int x = atoi("2147483647");
  return x + 1;
}
