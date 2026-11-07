// This file is part of the SV-Benchmarks collection of verification tasks:
// https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks
//
// SPDX-FileCopyrightText: 2026 The SV-Benchmarks Community
//
// SPDX-License-Identifier: Apache-2.0

#include <pthread.h>
#include <stdlib.h>

// A helper thread returns the shared buffer; the main thread writes to it
// without the lock while a reader thread is still running.
int shared_buf[4];
pthread_mutex_t m = PTHREAD_MUTEX_INITIALIZER;
int seen;

void *reader(void *arg) {
  pthread_mutex_lock(&m);
  seen = shared_buf[0];
  pthread_mutex_unlock(&m);
  return 0;
}

void *get_buffer(void *arg) {
  return shared_buf;
}

int main() {
  pthread_t r, t;
  void *res = 0;
  pthread_create(&r, 0, reader, 0);
  pthread_create(&t, 0, get_buffer, 0);
  pthread_join(t, &res);
  int *buf = res;
  if (buf != 0) {
    buf[0] = 1;
  }
  pthread_join(r, 0);
  return 0;
}
