// Under the bytes model a global without an initializer is zero at every byte offset.
// One object per fixture: under bytes, verification time grows quickly with the number of objects.
extern void abort(void);
void reach_error() { abort(); }

struct in { char c; int k; long l; };
struct out { short h; struct in n; int a[2]; };

struct out gz;

int main(void) {
  if (gz.n.k != 0 || gz.n.l != 0 || gz.a[1] != 0) reach_error();
  return 0;
}
