/*
 *  Copyright 2026 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
#include <pthread.h>
extern void reach_error(void);
extern void __VERIFIER_atomic_begin(void);
extern void __VERIFIER_atomic_end(void);
pthread_barrier_t barrier;
void *worker(void *arg) {
  pthread_barrier_wait(&barrier);
  return 0;
}
int main(void) {
  pthread_t thread;
  pthread_barrier_init(&barrier, 0, 2);
  pthread_create(&thread, 0, worker, 0);
  __VERIFIER_atomic_begin();
  int result = pthread_barrier_wait(&barrier);
  if (result == -1) reach_error();
  __VERIFIER_atomic_end();
  pthread_join(thread, 0);
  return 0;
}
