// Two hops through a recursive struct's self-pointer, the pointee was a placeholder `int`, so
// `sizeof(*a->next->next)` silently came out as 4 instead of the struct's size.
extern void abort(void);
extern void *malloc(unsigned long);
void reach_error() { abort(); }

typedef struct Node {
  int data;
  struct Node *next;
} Node;

int main() {
  Node *a = malloc(sizeof(Node));
  if (sizeof(*a->next) != sizeof(Node)) reach_error();
  if (sizeof(*a->next->next) != sizeof(Node)) reach_error();
  return 0;
}
