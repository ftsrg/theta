// This file is part of the SV-Benchmarks collection of verification tasks:
// https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks
//
// SPDX-FileCopyrightText: 2005-2021 University of Tartu & Technische Universität München
//
// SPDX-License-Identifier: MIT

#include <pthread.h>
#include <stdlib.h>

int* s;
pthread_mutex_t mutex = PTHREAD_MUTEX_INITIALIZER;

void *t_fun(void *arg) {
  s[0] = 8; // RACE!
  return NULL;
}

int main(void) {
  pthread_t id;
  s = (int*)malloc(sizeof(int));
  pthread_create(&id, NULL, t_fun, NULL);
  s[0] = 9; // RACE!
  pthread_join (id, NULL);
  return 0;
}