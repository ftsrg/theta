void reach_error(void) {}
struct H { void **vptr; };
void H_ser(struct H *h, long *c) { *c = 7; }
void H_deser(struct H *h, long *c) { reach_error(); }
void *vt_H[] = { (void*)0, (void*)0, (void*)&H_ser, (void*)&H_deser };
int main() { struct H h; long c = 0; h.vptr = (void**)&vt_H[2];
  void (*f)(void*, long*) = (void(*)(void*, long*))h.vptr[0]; f(&h, &c);
  if (c != 7) reach_error(); return 0; }
