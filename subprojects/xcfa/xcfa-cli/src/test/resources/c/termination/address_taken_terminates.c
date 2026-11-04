int main() {
  int b = 0;
  int *unused = &b;
  if (b != 0)
      while(1)
        ;
}
