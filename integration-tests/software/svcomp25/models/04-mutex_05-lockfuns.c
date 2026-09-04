// This file is part of the SV-Benchmarks collection of verification tasks:
// https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks
//
// SPDX-FileCopyrightText: 2005-2021 University of Tartu & Technische Universität München
//
// SPDX-License-Identifier: MIT

#include <pthread.h>
#include <stdio.h>

int myglobal;
pthread_mutex_t mutex = PTHREAD_MUTEX_INITIALIZER;

void lock() {
  pthread_mutex_lock(&mutex);
}

void unlock() {
  pthread_mutex_unlock(&mutex);
}


void *t_fun(void *arg) {
  lock();
  myglobal++; // NORACE
  unlock();
  return NULL;
}


int main(void) {
  pthread_t id;
  pthread_create(&id, NULL, t_fun, NULL);
  lock();
  myglobal++; // NORACE
  unlock();
  pthread_join (id, NULL);
  return 0;
}
