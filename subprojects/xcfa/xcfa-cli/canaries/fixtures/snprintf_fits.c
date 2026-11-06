// snprintf of a string that fits stays in the buffer
extern int snprintf(char *, unsigned long, const char *, ...);
int main() {
  char d[8];
  char s[4];
  s[0] = 65;
  s[1] = 65;
  s[2] = 65;
  s[3] = 0;
  snprintf(d, 8UL, "%s", s);
  return 0;
}
