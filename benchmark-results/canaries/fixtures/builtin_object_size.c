// batch 43: __builtin_object_size grammar rule + conservative fallback
char dst[8];
int main() {
  unsigned long n = __builtin_object_size(dst, 0);
  unsigned long m = __builtin_object_size(dst, 2);
  return (n == 0) + (m != 0);
}
