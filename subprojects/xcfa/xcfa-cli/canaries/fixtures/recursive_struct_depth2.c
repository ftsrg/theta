// A recursive struct's pointer to itself got an `int` pointee from the second hop on, so
// `a->next->next->data` failed with "Only structs expected here".
extern void abort(void);
extern void *malloc(unsigned long);
void reach_error() { abort(); }

typedef struct Node {
  int data;
  struct Node *next;
} Node;

int main() {
  Node *a = malloc(sizeof(Node));
  Node *b = malloc(sizeof(Node));
  Node *c = malloc(sizeof(Node));
  a->next = b;
  b->next = c;
  c->next = 0;
  c->data = 3;
  if (a->next->next->data != 3 || a->next->next->next != 0) reach_error();
  return 0;
}
