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
pthread_key_t key;
void *worker(void *arg) {
  if (pthread_getspecific(key) == 0) reach_error();
  return 0;
}
int main(void) {
  pthread_t thread;
  pthread_key_create(&key, 0);
  pthread_setspecific(key, (void *)16);
  pthread_create(&thread, 0, worker, 0);
  pthread_join(thread, 0);
  return 0;
}
