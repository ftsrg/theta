// A thread-creation loop may index its handle array with a file-scope counter:
// `pthread_create(&t[i], ...)` with a global `i`. CLibraryFunctionsPass keys a handle on a
// constant element index, so the counter has to be substituted into the unrolled copies --
// refusing that for every global left the index symbolic and failed the frontend outright.
extern void abort(void);
void reach_error() { abort(); }

typedef unsigned long int pthread_t;
union pthread_attr_t {
  char __size[56];
  long int __align;
};
typedef union pthread_attr_t pthread_attr_t;
extern int pthread_create(pthread_t *__restrict __newthread,
                          const pthread_attr_t *__restrict __attr,
                          void *(*__start_routine)(void *), void *__restrict __arg);
extern int pthread_join(pthread_t __th, void **__thread_return);

int i;
pthread_t t[2];

static void *worker(void *arg) { return arg; }

int main() {
  for (i = 0; i < 2; i++) pthread_create(&t[i], ((void *)0), &worker, ((void *)0));
  for (i = 0; i < 2; i++) pthread_join(t[i], ((void *)0));
  if (i != 2) reach_error();
  return 0;
}
