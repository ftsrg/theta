volatile int x; // boolean variable to test mutual exclusion

void *thr1(void *_) {
  x = 0;
  return 0;
}

void *thr2(void *_) {
  int i = x;
  return i;
}

void *thr3(void *_) {
  int i = x;
  return i;
}

void *thr4(void *_) {
  int i = x;
  return i;
}

void *thr5(void *_) {
  int i = x;
  return i;
}

void *thr6(void *_) {
  int i = x;
  return i;
}

void *thr7(void *_) {
  int i = x;
  return i;
}

void *thr8(void *_) {
  int i = x;
  return i;
}

void *thr9(void *_) {
  int i = x;
  return i;
}

void *thr10(void *_) {
  int i = x;
  return i;
}

void *thr11(void *_) {
  int i = x;
  return i;
}

void *thr12(void *_) {
  int i = x;
  return i;
}

void *thr13(void *_) {
  int i = x;
  return i;
}

void *thr14(void *_) {
  int i = x;
  return i;
}

void *thr15(void *_) {
  int i = x;
  return i;
}

void *thr16(void *_) {
  int i = x;
  return i;
}

void *thr17(void *_) {
  int i = x;
  return i;
}

void *thr18(void *_) {
  int i = x;
  return i;
}

int main() {
  pthread_t t1, t2;
  pthread_create(&t1, 0, thr1, 0);
  pthread_create(&t2, 0, thr2, 0);
  pthread_create(&t2, 0, thr3, 0);
  pthread_create(&t2, 0, thr4, 0);
  pthread_create(&t2, 0, thr5, 0);
  pthread_create(&t2, 0, thr6, 0);
  pthread_create(&t2, 0, thr7, 0);
  pthread_create(&t2, 0, thr8, 0);
  pthread_create(&t2, 0, thr9, 0);
  pthread_create(&t2, 0, thr10, 0);
  pthread_create(&t2, 0, thr11, 0);
  pthread_create(&t2, 0, thr12, 0);
  pthread_create(&t2, 0, thr13, 0);
  pthread_create(&t2, 0, thr14, 0);
  pthread_create(&t2, 0, thr15, 0);
  pthread_create(&t2, 0, thr16, 0);
  pthread_create(&t2, 0, thr17, 0);
  pthread_create(&t2, 0, thr18, 0);
  return 0;
}
