// A postfix ++/-- in an operand of && or || takes effect only if that operand is evaluated, and
// before the next operand: the update used to wait for the end of the whole expression, unguarded.
extern void abort(void);
void reach_error() { abort(); }

int main() {
  int x = 0, y = 0;
  int b = (x == 0) || y++;           /* skipped */
  if (y != 0) reach_error();
  if (x != 0 && y--) reach_error();  /* skipped */
  if (y != 0) reach_error();

  int stop = 1, n = 3;
  while (!stop && n--) { }           /* skipped in a loop condition */
  if (n != 3) reach_error();

  x = 1;
  b = x++ && (x == 2);               /* the right operand sees the update */
  if (!b || x != 2) reach_error();

  n = 1;
  b = (n > 0) && n--;                /* but the operands' values are taken before it */
  if (!b || n != 0) reach_error();

  char s[4] = {1, 1, 0, 5};
  char *p = s;
  while (*p != 0 && p++) { }         /* stops at s[2] without stepping past it */
  if (*p != 0) reach_error();
  return 0;
}
