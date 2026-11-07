/*
 * This file is part of the SV-Benchmarks collection of verification tasks:
 * https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks
 *
 * SPDX-FileCopyrightText: 2026 Technical University of Munich
 *
 * SPDX-License-Identifier: MIT
 */

#include<pthread.h>
#include<stdio.h>
#include<assert.h>

extern void abort();
void reach_error() { assert(0); }
void __VERIFIER_assert(int cond) { if(!(cond)) { reach_error(); abort(); } }
extern int __VERIFIER_nondet_int();

pthread_barrier_t barrier;

// The mutex permits only one waiter, which can still pass when input selects capacity one.

unsigned int get_capacity(int argc) {
    return argc > 1 ? 2 : 1;
}

pthread_mutex_t mutex = PTHREAD_MUTEX_INITIALIZER;

void* f1(void* ptr) {
    pthread_mutex_lock(&mutex);
    pthread_barrier_wait(&barrier);
    pthread_mutex_unlock(&mutex);
    return NULL;
}

int main(int argc, char const *argv[])
{
    int top = __VERIFIER_nondet_int();
    int i = 0;

    unsigned int capacity = get_capacity(argc);

    pthread_barrier_init(&barrier, NULL, capacity);

    pthread_t t1;
    pthread_create(&t1,NULL,f1,NULL);

    if(top) {
        pthread_mutex_lock(&mutex);
        pthread_barrier_wait(&barrier);
        pthread_mutex_unlock(&mutex);
        i = 1;
    }

    __VERIFIER_assert(i == 0);

    return 0;
}
