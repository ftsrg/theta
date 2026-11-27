// an address-taken global union spans the cells its initialization writes
union U { int a[6]; char c[24]; long l; };
union U u;
void touch(union U *p) { p->a[1] = 3; }
int main() {
  touch(&u);
  return u.a[1] == 3 ? 0 : 1;
}
