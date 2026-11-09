// The address of a heap struct's first member is the block's address, so freeing it is valid,
// even when the member is an array that the cell models keep as a separate object.
void *malloc(unsigned long);
void free(void *);
void abort(void);
typedef void *item_t[2];
struct item {
  item_t head;
  char text[16];
};

int main(void) {
  struct item *item = malloc(sizeof *item);
  if (!item) abort();
  item->head[0] = 0;
  item->text[0] = '\0';
  item_t *head = &item->head;
  free(head);
  return 0;
}
