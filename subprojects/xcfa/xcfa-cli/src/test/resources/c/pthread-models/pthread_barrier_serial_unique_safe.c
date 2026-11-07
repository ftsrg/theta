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
pthread_barrier_t barrier;
int worker_result;
void *worker(void *arg) {
  worker_result = pthread_barrier_wait(&barrier);
  return 0;
}
int main(void) {
  pthread_t thread;
  pthread_barrier_init(&barrier, 0, 2);
  pthread_create(&thread, 0, worker, 0);
  int result = pthread_barrier_wait(&barrier);
  pthread_join(thread, 0);
  if (!((result == -1 && worker_result == 0) ||
        (result == 0 && worker_result == -1))) reach_error();
  return 0;
}
