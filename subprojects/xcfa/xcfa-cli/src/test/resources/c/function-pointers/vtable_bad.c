void reach_error(void) {}
struct Cdr { int x; };
struct H { void **vptr; };
void H_ser(struct H *h, struct Cdr *c) {}
void H_deser(struct H *h, struct Cdr *c) { reach_error(); }
void *vt_H[] = { (void*)0, (void*)0, (void*)&H_ser, (void*)&H_deser };
void vcall(void* obj, int slot, void* first, struct Cdr* a0) {
  void* fn = ((void**)*(void**)obj)[slot];
  void (*f)(void*, struct Cdr*) = (void(*)(void*, struct Cdr*))fn;
  f(first, a0);
}
int main() { struct H h; struct Cdr c; h.vptr = (void**)&vt_H[2]; vcall(&h, 1, &h, &c); return 0; }
