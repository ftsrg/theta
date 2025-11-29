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
void reach_error() { __assert_fail("0", "loop-tiling-eq.wvr.c", 21, __extension__ __PRETTY_FUNCTION__); }
extern int pthread_create (pthread_t *__restrict __newthread,
      const pthread_attr_t *__restrict __attr,
      void *(*__start_routine) (void *),
      void *__restrict __arg) __attribute__ ((__nothrow__)) __attribute__ ((__nonnull__ (1, 3)));
extern int pthread_join (pthread_t __th, void **__thread_return);

typedef unsigned int size_t;
extern void *malloc (size_t __size) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;

extern int  __VERIFIER_nondet_int(void);
extern void __VERIFIER_atomic_begin(void);
extern void __VERIFIER_atomic_end(void);

extern void abort(void);
void assume_abort_if_not(int cond) {
  if(!cond) {abort();}
}

int** B;
int*  A;
int*  F;
int L, N, M, a, b;

int *create_fresh_int_array(int size);

void* thread1(void* _argptr) {
  for (int i=0; i<L; i++) {
    A[i] = F[i];
  }

  return 0;
}

void* thread2(void* _argptr) {
  for (int i=0; i<N; i++) {
    for (int j=0; j<M; j++) {
      B[i][j] = F[i*M+j];
    }
  }

  return 0;
}

int main() {
  pthread_t t1, t2;

  // initialize global variables
  M = __VERIFIER_nondet_int();
  assume_abort_if_not(M >= 0);
  N = __VERIFIER_nondet_int();
  assume_abort_if_not(N >= 0);

  assume_abort_if_not(N == 0 || M <= 2147483647 / N);
  L = M * N;
  A = create_fresh_int_array(L);
  F = create_fresh_int_array(L);
  assume_abort_if_not(N <= (((size_t) 4294967295) / sizeof(int*)));
  B = (int**)malloc(sizeof(int*) * (size_t)N);
  for (int i=0; i<N; i++) {
    B[i] = create_fresh_int_array(M);
  }
  
  // main method
  pthread_create(&t1, 0, thread1, 0);
  pthread_create(&t2, 0, thread2, 0);
  pthread_join(t1, 0);
  pthread_join(t2, 0);
  
  a = __VERIFIER_nondet_int();
  b = __VERIFIER_nondet_int();
  assume_abort_if_not(a >= 0 && a < N && b >= 0 && b < M);
  assume_abort_if_not(A[a*M+b] != B[a][b]);
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
