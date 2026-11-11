// Freeing a member that does not start the block is an invalid free.
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
  free(item->text);
  return 0;
}
