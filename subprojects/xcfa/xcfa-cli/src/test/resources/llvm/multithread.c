#include <pthread.h>
void* p0(void* param) {
    volatile int i = 0;
}
void* p1(void* param) {
    while(1) {
    volatile int j = 0;
    }
}

int main() {
    pthread_t t1, t2;

    pthread_create(&t1, 0, p0, 0);
    pthread_create(&t2, 0, p1, 0);

    pthread_join(t1, 0);
    pthread_join(t2, 0);
}
