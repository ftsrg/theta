// The Juliet fgets/atoi pattern: the input can be any number that fits the line.
typedef struct _IO_FILE FILE;
extern FILE *stdin;
extern char *fgets(char *s, int n, FILE *stream);
extern int atoi(const char *s);

int main() {
  int data = 0;
  char b[6];
  if (fgets(b, 6, stdin) != 0) data = atoi(b);
  return data * 1000000;
}
