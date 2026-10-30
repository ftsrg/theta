extern void abort(void);
void reach_error(void) { abort(); }

#include <stdlib.h>

struct list_head {
  struct list_head *next;
  struct list_head *prev;
};

struct node {
  int value;
  struct list_head linkage;
  struct list_head nested;
};

int main(void) {
  struct node *node = malloc(sizeof(*node));
  if (node == 0) return 0;

  node->nested.next = &node->nested;
  node->nested.prev = &node->nested;
  if (node->nested.next != &node->nested) reach_error();
  if (node->nested.prev != &node->nested) reach_error();
  if (node->nested.next == &node->linkage) reach_error();
  if (node->nested.prev == &node->linkage) reach_error();
  return 0;
}
