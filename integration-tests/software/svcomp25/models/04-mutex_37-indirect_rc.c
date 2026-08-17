// This file is part of the SV-Benchmarks collection of verification tasks:
// https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks
//
// SPDX-FileCopyrightText: 2005-2021 University of Tartu & Technische Universität München
//
// SPDX-License-Identifier: MIT

#include <pthread.h>

int g;
int *g1;
int *g2;
pthread_mutex_t mutex = PTHREAD_MUTEX_INITIALIZER;

void *t_fun(void *arg) {
  pthread_mutex_lock(&mutex);
  (*g1)++; // RACE!
  pthread_mutex_unlock(&mutex);
  return NULL;
}

int main(void) {
  pthread_t id;
  int x;
  g1 = g2 = &g;

  pthread_create(&id, NULL, t_fun, NULL);

  (*g2)++; // RACE!

  pthread_join (id, NULL);
  return 0;
}
