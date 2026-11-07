// Each _Bool member occupies a byte of its struct.
extern void abort(void);
void reach_error() { abort(); }

struct S {
  _Bool a;
  _Bool b;
  char c;
};

struct S s;

int main(void) {
  if (sizeof(struct S) != 3) reach_error();
  if ((char *)&s.c - (char *)&s != 2) reach_error();
  s.a = 1;
  s.b = 0;
  s.c = 0;
  if (s.a != 1) reach_error();
  return 0;
}
