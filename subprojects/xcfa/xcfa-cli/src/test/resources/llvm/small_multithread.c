volatile int x; // boolean variable to test mutual exclusion

void *thr1(void *_) {
  x = 0;
  x = 1;
  return 0;
}

void *thr2(void *_) {
  int i = x, j = x;
  return i+j;
}

int main() {
  pthread_t t1, t2;
  pthread_create(&t1, 0, thr1, 0);
  pthread_create(&t2, 0, thr2, 0);
  pthread_join(t1, 0);
  pthread_join(t2, 0);
  return 0;
}
