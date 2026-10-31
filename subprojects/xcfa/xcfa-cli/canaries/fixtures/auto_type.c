// GNU `__auto_type x = e` declares x with the type of e.
extern void abort(void);
void reach_error(){ abort(); }

long y;

int main(void) {
  __auto_type c = (char)-1;
  if (sizeof(c) != 1) reach_error();
  if (c >= 0) reach_error();

  __auto_type p = &y;
  *p = 5;
  if (y != 5) reach_error();

  __auto_type q = p;
  if (sizeof(*q) != sizeof(long)) reach_error();
  if (*q != 5) reach_error();

  __auto_type i = 1;
  __auto_type l = i + 1L;
  __auto_type u = 3u;
  if (sizeof(i) != sizeof(int)) reach_error();
  if (sizeof(l) != sizeof(long)) reach_error();
  if (l != 2) reach_error();
  if (u - 4 < 0) reach_error();
  return 0;
}
