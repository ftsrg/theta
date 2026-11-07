extern void reach_error(void);
int a[3];
int main(void) {
  a[1] = 0;
  void* v = a;
  char* c = (char*)v;
  c = c + 4;
  int* q = (int*)c;
  *q = 5;
  if (a[1] != 5)
    reach_error();
  return 0;
}
