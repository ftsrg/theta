// The second call of the `||` is skipped when the first operand holds, leaving its return variable
// unassigned on that path, which is the only one reaching the error (c == 1 after the join).
typedef unsigned long int pthread_t;
typedef union {
  char __size[36];
  long int __align;
} pthread_attr_t;
extern int pthread_create(pthread_t *__newthread, const pthread_attr_t *__attr,
                          void *(*__start_routine)(void *), void *__arg);
extern int pthread_join(pthread_t __th, void **__thread_return);
void reach_error() {}

int c = 0;
int flag = 1;

void *thr(void *arg) {
  c = 1;
  return 0;
}

int get(int *p) { return *p; }

int main(void) {
  pthread_t id;
  pthread_create(&id, 0, thr, 0);
  pthread_join(id, 0);
  if (get(&c) != 2 || get(&flag) != 1) reach_error();
  return 0;
}
