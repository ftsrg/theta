// This file is part of the SV-Benchmarks collection of verification tasks:
// https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks
//
// SPDX-FileCopyrightText: 2005-2021 University of Tartu & Technische Universität München
//
// SPDX-License-Identifier: MIT

#include <pthread.h>

int data;
int *p = &data, *q;

pthread_mutex_t mutex = PTHREAD_MUTEX_INITIALIZER;

void *t_fun(void *arg) {
  pthread_mutex_lock(&mutex);
  *p = 8; // NORACE
  pthread_mutex_unlock(&mutex);
  return NULL;
}

int main() {
  pthread_t id;
  pthread_create(&id, NULL, t_fun, NULL);
  q = p; // NORACE
  pthread_mutex_lock(&mutex);
  *q = 8; // NORACE
  pthread_mutex_unlock(&mutex);
  return 0;
}
