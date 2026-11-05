// An array's element count is 10, so this reaches the error: a size that is too small would hide it.
extern void abort(void);
void reach_error() { abort(); }

int global[10];

int main() {
  if (sizeof(global) / sizeof(global[0]) == 10) reach_error();
  return 0;
}
