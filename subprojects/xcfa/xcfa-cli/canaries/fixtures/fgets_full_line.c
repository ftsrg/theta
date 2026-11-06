// fgets can read a line of n - 1 characters.
extern void abort(void);
void reach_error() { abort(); }
typedef struct _IO_FILE FILE;
extern FILE *stdin;
extern char *fgets(char *s, int n, FILE *stream);
extern unsigned long strlen(const char *s);

int main() {
  char buf[8];
  if (fgets(buf, 8, stdin) == 0) return 0;
  if (strlen(buf) == 7) reach_error();
  return 0;
}
