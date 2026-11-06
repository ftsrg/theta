// snprintf with a size beyond the buffer writes past it
extern int snprintf(char *, unsigned long, const char *, ...);
int main() {
  char d[4];
  char s[8];
  for (int i = 0; i < 7; i++) s[i] = 65;
  s[7] = 0;
  snprintf(d, 8UL, "%s", s);
  return 0;
}
