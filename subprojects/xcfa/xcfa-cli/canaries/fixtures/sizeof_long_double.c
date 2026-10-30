// The width of a floating type is looked up by its name, and `long double` is spelled with a space
// while the architecture table's key is not. It is modelled as binary128, so its size is 16 bytes.
extern void abort(void);
void reach_error(){ abort(); }

int main() {
  long double x = 1.5L;
  if (sizeof(long double) != 16) reach_error();
  if (sizeof x != 16) reach_error();
  if (sizeof 1.5L != 16) reach_error();
  return 0;
}
