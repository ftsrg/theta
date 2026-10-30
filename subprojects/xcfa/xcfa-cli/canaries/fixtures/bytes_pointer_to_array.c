// Under bytes, an object whose address is taken (`&list`) is sized in bytes like every other
// object; sizing it in cells made `(*l)[i]` look out of bounds.
void *list[2];

int main(void) {
  void *(*l)[2] = &list;
  void *p = (*l)[1];
  return p != 0;
}
