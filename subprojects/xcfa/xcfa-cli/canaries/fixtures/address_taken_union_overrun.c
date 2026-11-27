// an address-taken global union is bounded by its own size
union U { int a[6]; char c[24]; long l; };
union U u;
void touch(union U *p) { p->a[6] = 3; }
int main() {
  touch(&u);
  return 0;
}
