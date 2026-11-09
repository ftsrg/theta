extern void *malloc(unsigned long);
extern void free(void *);
extern void abort(void);
extern void *memcpy(void *, const void *, unsigned long);
struct Buf { unsigned char *data; unsigned long len; };
void Buf__Buf(struct Buf *this, unsigned char *src, unsigned long n) {
  this->data = malloc(n);
  if (!this->data) abort();
  memcpy(this->data, src, n);
  this->len = n;
}
void Buf___Buf(struct Buf *this) { free(this->data); }
unsigned char Buf__get(struct Buf *this, unsigned long i) { return i < this->len ? this->data[i] : 0; }
unsigned char Buf__head(struct Buf *this) { return this->data[0]; }
