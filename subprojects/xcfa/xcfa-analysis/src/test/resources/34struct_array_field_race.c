// Plain stores to the nested fields of the same element of an array of structs.
typedef unsigned long int pthread_t;
extern int pthread_create(pthread_t *thread, const void *attr, void *(*start)(void *), void *arg);
extern int pthread_join(pthread_t thread, void **ret);

typedef struct { void *v; } vp;
typedef struct { vp next; vp locked; } node_t;
node_t nodes[2];

void w(vp *a) { a->v = (void *)0; }
void w2(node_t *n) {
  w(&n->next);
  w(&n->locked);
}
void *t(void *arg) {
  unsigned int tid = (unsigned long)arg;
  w2(&nodes[tid]);
  return 0;
}

int main(void) {
  pthread_t a, b;
  pthread_create(&a, 0, t, (void *)1);
  pthread_create(&b, 0, t, (void *)1);
  pthread_join(a, 0);
  pthread_join(b, 0);
  return 0;
}
