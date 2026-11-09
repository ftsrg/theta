// sizeof of an array object is its whole size: the element size times the dimensions, or the
// initializer's extent. Forms that decay to a pointer, and array parameters, stay pointer-sized.
extern void abort(void);
void reach_error() { abort(); }

struct S {
  int a[10];
  int b;
};

int global[10];
int initialized[] = {1, 2, 3};
int matrix[2][3];
char string[] = "abcdefghi";
struct S st;
typedef int Row[10];
Row row;

int parameterSize(int a[10]) { return sizeof(a); }

int main() {
  int local[7];
  if (sizeof(global) != 10 * sizeof(int)) reach_error();
  if (sizeof(global) / sizeof(global[0]) != 10) reach_error();
  if (sizeof(initialized) / sizeof(initialized[0]) != 3) reach_error();
  if (sizeof(matrix) != 6 * sizeof(int)) reach_error();
  if (sizeof(matrix[0]) != 3 * sizeof(int)) reach_error();
  if (sizeof(*matrix) != 3 * sizeof(int)) reach_error();
  if (sizeof(string) != 10) reach_error();
  if (sizeof("abcdefghi") != 10) reach_error();
  if (sizeof(st.a) != 10 * sizeof(int)) reach_error();
  if (sizeof(row) != 10 * sizeof(int)) reach_error();
  if (sizeof(Row) != 10 * sizeof(int)) reach_error();
  if (sizeof local != 7 * sizeof(int)) reach_error();

  if (sizeof(global + 1) != sizeof(int *)) reach_error();
  if (sizeof(1 ? global : global) != sizeof(int *)) reach_error();
  if (sizeof((0, global)) != sizeof(int *)) reach_error();
  if (parameterSize(global) != sizeof(int *)) reach_error();
  return 0;
}
