// This file is part of the SV-Benchmarks collection of verification tasks:
// https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks
//
// SPDX-FileCopyrightText: 2005-2021 University of Tartu & Technische Universität München
//
// SPDX-License-Identifier: MIT

#include <assert.h>
extern void abort(void);
void reach_error() { assert(0); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }

#include<pthread.h>

int glob1 = 5;
pthread_mutex_t mutex1 = PTHREAD_MUTEX_INITIALIZER;
pthread_mutex_t mutex2 = PTHREAD_MUTEX_INITIALIZER;

void *t_fun(void *arg) {
  int t;
  pthread_mutex_lock(&mutex1);
  t = glob1;
  __VERIFIER_assert(t == 5);
  glob1 = -10;
  __VERIFIER_assert(glob1 == -10);
  glob1 = t;
  pthread_mutex_unlock(&mutex1);
  return NULL;
}

int main(void) {
  pthread_t id;
  __VERIFIER_assert(glob1 == 5);
  pthread_create(&id, NULL, t_fun, NULL);
  pthread_mutex_lock(&mutex1);
  glob1++; 
  __VERIFIER_assert(glob1 == 6);
  glob1--;
  pthread_mutex_unlock(&mutex1);
  pthread_join (id, NULL);
  return 0;
}
