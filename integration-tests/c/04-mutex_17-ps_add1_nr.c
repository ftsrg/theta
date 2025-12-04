// This file is part of the SV-Benchmarks collection of verification tasks:
// https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks
//
// SPDX-FileCopyrightText: 2005-2021 University of Tartu & Technische Universität München
//
// SPDX-License-Identifier: MIT

extern int __VERIFIER_nondet_int();

#include<stdio.h>
#include<pthread.h>
#include<assert.h>
#include<limits.h>

int glob;
pthread_mutex_t m = PTHREAD_MUTEX_INITIALIZER;

void *t_fun(void *arg) {
  pthread_mutex_lock(&m);
  glob++; // NORACE
  pthread_mutex_unlock(&m);
  return NULL;
}

int main() {
  int i = __VERIFIER_nondet_int();
  pthread_t id;
  pthread_create(&id, NULL, t_fun, NULL);

  if (i == INT_MAX) {
    return 0;
  }

  printf("Do the work? ");
  if (i)
    pthread_mutex_lock(&m);
  printf("Now we do the work..\n");
  i++;
  if (i-1)
    glob++; // NORACE
  printf("Work is completed...");
  i--;
  if (i)
    pthread_mutex_unlock(&m);

  return 0;
}
