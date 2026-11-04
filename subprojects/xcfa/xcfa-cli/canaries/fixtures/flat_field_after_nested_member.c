// The field after an inline struct member lies within the object: a referenced global is sized in
// cells, not fields.
struct inner {
  int x;
  int y;
};
struct outer {
  int first;
  struct inner nested;
  int last;
} global;

int main(void) {
  struct outer *o = &global;
  o->last = 1;
  return 0;
}
