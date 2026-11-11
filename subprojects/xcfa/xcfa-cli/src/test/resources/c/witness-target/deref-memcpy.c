void *malloc(unsigned long size);
void *memcpy(void *dest, const void *src, unsigned long n);
void free(void *ptr);
int main(void) {
  char *p = malloc(4);
  memcpy(p, "abc", 4); // target: memcpy(p, "abc", 4)
  free(p);
  return 0;
}
