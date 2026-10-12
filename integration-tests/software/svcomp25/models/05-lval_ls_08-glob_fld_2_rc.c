// This file is part of the SV-Benchmarks collection of verification tasks:
// https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks
//
// SPDX-FileCopyrightText: 2005-2021 University of Tartu & Technische Universität München
//
// SPDX-License-Identifier: MIT

#include <pthread.h>

struct {
  int x;
  int y;
} data;

void *t_fun(void *arg) {
  data.x++; // RACE!
  return NULL;
}

int main() {
  pthread_t id, id2;
  pthread_create(&id, NULL, t_fun, NULL);
  pthread_create(&id2, NULL, t_fun, NULL);
  data.y++; // NORACE
  return 0;
}

