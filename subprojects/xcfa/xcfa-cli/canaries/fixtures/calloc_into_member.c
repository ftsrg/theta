// calloc stored straight into a member is still zeroed.
extern void *calloc(unsigned long, unsigned long);
extern void abort(void);
void reach_error() { abort(); }
struct node { int v; struct node *next; };
int main() {
  struct node *h = (struct node *)calloc(1, sizeof(struct node));
  if (!h) return 0;
  h->next = (struct node *)calloc(1, sizeof(struct node));
  if (h->next && h->next->v != 0) reach_error();
  return 0;
}
