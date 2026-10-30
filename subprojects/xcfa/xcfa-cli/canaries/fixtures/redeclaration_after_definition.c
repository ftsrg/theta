// A redeclaration without an initializer used to replace the definition before it, dropping its
// initializer. The declaration with an initializer is the definition, whatever the order.
extern void abort(void);
void reach_error() { abort(); }

int x = 5;
extern int x;

int arr[3] = {1, 2, 3};
extern int arr[];

int y = 7;
int z;
extern int y, z; // visited for z, it must not re-initialize y

int a, b; // visited for b, it must not re-initialize a
int a = 1;

int main() {
  if (x != 5) reach_error();
  if (arr[1] != 2) reach_error();
  if (y != 7 || z != 0) reach_error();
  if (a != 1 || b != 0) reach_error();
  return 0;
}
