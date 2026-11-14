// memcpy between same-size structs of different cell layouts must not be walked by the destination's
// cells: struct A has fewer cells than struct B, so that walk read past the source (false alarm)
typedef unsigned int size_t;
extern void *memcpy(void *__restrict, const void *__restrict, size_t);
extern void *malloc(size_t);
extern void free(void *);
extern void abort(void);

struct A {
  unsigned char a;
  unsigned char b : 2;
  unsigned char c : 2;
  unsigned char d : 4;
  unsigned char e : 4;
  unsigned char pad;
  unsigned int f;
} __attribute__((packed));

struct B {
  unsigned char a;
  unsigned char b : 2;
  unsigned char c : 2;
  unsigned char d : 4;
  unsigned char e, f, f1, f2, f3, f4;
} __attribute__((packed));

struct A d = {.b = 3};

int main(void) {
  struct B *p = malloc(sizeof(struct B));
  if (!p) abort();
  memcpy(p, &d, sizeof(struct B));
  free(p);
  return 0;
}
