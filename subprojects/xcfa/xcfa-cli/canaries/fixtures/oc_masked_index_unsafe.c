// A masked index reaches every slot its mask allows.
extern void reach_error(void); typedef unsigned long int pthread_t; extern int pthread_create(pthread_t *t, const void *a, void *(*s)(void *), void *arg); extern int pthread_join(pthread_t t, void **r);
int ring[4];
int head;
void *w(void *arg) { head = head + 3; return 0; }
int main(void) {
  pthread_t t;
  pthread_create(&t, 0, w, 0);
  pthread_join(t, 0);
  ring[head & 3] = 9;
  if (ring[3] == 9) reach_error();
  return 0;
}
