// sizeof over an array *type name* is the element size times the dimensions. The array part of the
// type name used to be dropped, so `sizeof(int[4])` came out as `sizeof(int)`.
extern void abort(void);
void reach_error() { abort(); }

struct Node {
  int v;
  struct Node *next;
};
typedef struct Node node_t;

int main() {
  if (sizeof(int[4]) != 4 * sizeof(int)) reach_error();
  if (sizeof(int[2][3]) != 6 * sizeof(int)) reach_error();
  if (sizeof(char[10]) != 10) reach_error();
  if (sizeof(int *[4]) != 4 * sizeof(int *)) reach_error();
  if (sizeof(struct Node[3]) != 3 * sizeof(struct Node)) reach_error();
  if (sizeof(node_t[3]) != 3 * sizeof(node_t)) reach_error();
  return 0;
}
