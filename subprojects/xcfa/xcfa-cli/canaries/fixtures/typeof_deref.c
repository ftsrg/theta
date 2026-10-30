// typeof(*p) names the pointee, not the pointer -- also when nested, as in the kernel's
// list_for_each_entry/container_of form `typeof(((typeof(*m) *)0)->list)`.
extern void abort(void);
void reach_error() { abort(); }

struct list_head { struct list_head *next, *prev; };
struct el { int e; struct list_head list; };

int main() {
  struct el node;
  struct el *m = &node;
  int *p = &node.e;

  typeof(*m) copy;                              /* a struct el, so it has members */
  copy.e = 1;
  if (copy.e != 1) reach_error();

  typeof(*p) d = 1;                             /* an int, not an int * */
  if (sizeof(d) != sizeof(int)) reach_error();

  const typeof(((typeof(*m) *)0)->list) *pos = &node.list;
  if (pos != &node.list) reach_error();
  return 0;
}
