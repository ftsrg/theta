#include <pthread.h>
#include <stdatomic.h>

_Atomic int i;
void* p0(void* param) {
    atomic_store_explicit(&i, 1, memory_order_release);
}
void* p1(void* param) {
    atomic_store_explicit(&i, atomic_read_explicit(&i, memory_order_acquire), memory_order_release);
}

int main() {
    pthread_t t1, t2;

    pthread_create(&t1, 0, p0, 0);
    pthread_create(&t2, 0, p1, 0);

    pthread_join(t1, 0);
    pthread_join(t2, 0);
}
