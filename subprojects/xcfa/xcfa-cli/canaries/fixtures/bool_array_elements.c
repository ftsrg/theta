// The elements of a _Bool array are distinct objects.
extern void abort(void);
void reach_error() { abort(); }

_Bool arr[2];

int main(void) {
  arr[0] = 1;
  arr[1] = 0;
  if (arr[0] != 1) reach_error();
  return 0;
}
