// A line of at most 3 characters holds no number above 999.
extern void abort(void);
void reach_error() { abort(); }
typedef struct _IO_FILE FILE;
extern FILE *stdin;
extern char *fgets(char *s, int n, FILE *stream);
extern int atoi(const char *s);

int main() {
  char b[4];
  if (fgets(b, 4, stdin) == 0) return 0;
  if (atoi(b) > 999) reach_error();
  return 0;
}
