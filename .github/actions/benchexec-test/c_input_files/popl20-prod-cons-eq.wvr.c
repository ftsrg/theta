// This file is part of the SV-Benchmarks collection of verification tasks:
// https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks
//
// SPDX-FileCopyrightText: 2021 F. Schuessele <schuessf@informatik.uni-freiburg.de>
// SPDX-FileCopyrightText: 2021 D. Klumpp <klumpp@informatik.uni-freiburg.de>
//
// SPDX-License-Identifier: LicenseRef-BSD-3-Clause-Attribution-Vandikas

typedef unsigned long int pthread_t;

union pthread_attr_t
{
  char __size[36];
  long int __align;
};
typedef union pthread_attr_t pthread_attr_t;

extern void __assert_fail(const char *__assertion, const char *__file,
      unsigned int __line, const char *__function)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "popl20-prod-cons-eq.wvr.c", 21, __extension__ __PRETTY_FUNCTION__); }
extern int pthread_create (pthread_t *__restrict __newthread,
      const pthread_attr_t *__restrict __attr,
      void *(*__start_routine) (void *),
      void *__restrict __arg) __attribute__ ((__nothrow__)) __attribute__ ((__nonnull__ (1, 3)));
extern int pthread_join (pthread_t __th, void **__thread_return);

typedef unsigned int size_t;
extern void *malloc (size_t __size) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;

extern int  __VERIFIER_nondet_int(void);
extern _Bool __VERIFIER_nondet_bool(void);
extern void __VERIFIER_atomic_begin(void);
extern void __VERIFIER_atomic_end(void);

extern void abort(void);
void assume_abort_if_not(int cond) {
  if(!cond) {abort();}
}

int *produce, *update, *queue1, **consume;
_Bool *done;
int front1, size1, state11, state12, state21, state22;
int n_queue, n_produce, n_update, n1, n2;
_Bool finished1, finished2;

int *create_fresh_int_array(int size);
_Bool *create_fresh_bool_array(int size);

void* thread1(void* _argptr) {
  while (!finished1) {
    __VERIFIER_atomic_begin();
    assume_abort_if_not(front1+size1 >= 0 && front1+size1 < n_queue);
    assume_abort_if_not(state11 >= 0 && state11 < n_produce);
    assume_abort_if_not(queue1[front1+size1] == produce[state11]);
    size1++;
    __VERIFIER_atomic_end();
    assume_abort_if_not(state11 >= 0 && state11 < n_update);
    state11 = update[state11];
    assume_abort_if_not(state11 >= 0 && state11 < n_update);
    __VERIFIER_atomic_begin();
    finished1 = done[state11];
    __VERIFIER_atomic_end();
  }

  return 0;
}

void* thread2(void* _argptr) {
  __VERIFIER_atomic_begin();
  _Bool cond = !finished1 || size1 > 0;
  __VERIFIER_atomic_end();
  while (cond) {
    __VERIFIER_atomic_begin();
    assume_abort_if_not(size1 > 0);
    assume_abort_if_not(state12 >= 0 && state12 < n1);
    assume_abort_if_not(front1 >= 0 && front1 < n_queue);
    assume_abort_if_not(queue1[front1] >= 0 && queue1[front1] < n2);
    state12 = consume[state12][queue1[front1]];
    front1++;
    size1--;
    __VERIFIER_atomic_end();
    __VERIFIER_atomic_begin();
    cond = !finished1 || size1 > 0;
    __VERIFIER_atomic_end();
  }

  return 0;
}

void* thread3(void* _argptr) {
  while (!finished2) {
    assume_abort_if_not(state22 >= 0 && state22 < n1);
    assume_abort_if_not(state21 >= 0 && state21 < n_produce);
    assume_abort_if_not(produce[state21] >= 0 && produce[state21] < n2);
    state22 = consume[state22][produce[state21]];
    assume_abort_if_not(state21 >= 0 && state21 < n_update);
    state21 = update[state21];
    assume_abort_if_not(state21 >= 0 && state21 < n_update);
    finished2 = done[state21];
  }

  return 0;
}

int main() {
  pthread_t t1, t2, t3;

  front1 = __VERIFIER_nondet_int();
  state11 = __VERIFIER_nondet_int();
  state21 = state11;
  state12 = __VERIFIER_nondet_int();
  state22 = state12;

  n_queue = __VERIFIER_nondet_int();
  n_produce = __VERIFIER_nondet_int();
  n_update = __VERIFIER_nondet_int();
  n1 = __VERIFIER_nondet_int();
  n2 = __VERIFIER_nondet_int();

  produce = create_fresh_int_array(n_produce);
  update = create_fresh_int_array(n_update);
  queue1 = create_fresh_int_array(n_queue);
  done = create_fresh_bool_array(n_update);
  assume_abort_if_not(n1 >= 0);
  assume_abort_if_not(n1 <= (((size_t) 4294967295) / sizeof(int*)));
  consume = (int**)malloc(sizeof(int*) * (size_t)n1);
  for (int i=0; i<n1; i++) {
    consume[i] = create_fresh_int_array(n2);
  }

  // main method
  pthread_create(&t1, 0, thread1, 0);
  pthread_create(&t2, 0, thread2, 0);
  pthread_create(&t3, 0, thread3, 0);
  pthread_join(t1, 0);
  pthread_join(t2, 0);
  pthread_join(t3, 0);

  assume_abort_if_not(state12 != state22);
  reach_error();

  return 0;
}

int *create_fresh_int_array(int size) {
  assume_abort_if_not(size >= 0);
  assume_abort_if_not(size <= (((size_t) 4294967295) / sizeof(int)));

  int* arr = (int*)malloc(sizeof(int) * (size_t)size);
  for (int i = 0; i < size; i++) {
    arr[i] = __VERIFIER_nondet_int();
  }
  return arr;
}

_Bool *create_fresh_bool_array(int size) {
  assume_abort_if_not(size >= 0);
  assume_abort_if_not(size <= (((size_t) 4294967295) / sizeof(_Bool)));

  _Bool* arr = (_Bool*)malloc(sizeof(_Bool) * (size_t)size);
  for (int i = 0; i < size; i++) {
    arr[i] = __VERIFIER_nondet_bool();
  }
  return arr;
}
