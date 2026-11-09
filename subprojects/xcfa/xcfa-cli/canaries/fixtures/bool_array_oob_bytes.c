// A _Bool occupies a byte. With a 1-bit storage size its elements had stride 0 under bytes, so
// every element aliased the first and no index was out of bounds.
typedef unsigned int size_t;
extern void *malloc(size_t size);
extern void abort(void);

_Bool *done;

int main(void) {
  done = (_Bool *)malloc(sizeof(_Bool) * 2);
  if (done == 0) abort();
  int b = done[100];
  return b;
}
