// strcpy copies the terminating null byte, so the destination is a valid string afterwards.
extern void abort(void);
void reach_error() { abort(); }
extern char *strcpy(char *, const char *);
int main(void) {
  char dst[4];
  strcpy(dst, "AB");
  if (dst[0] != 'A' || dst[1] != 'B' || dst[2] != 0) reach_error();
  return 0;
}
