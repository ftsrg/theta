// No stub writes a buffer, so strlen is a loop over the cells, and its result is not recorded.
extern unsigned long strlen(const char *s);

int main() {
  char a[4] = "abc";
  return (int)strlen(a) + 1;
}
