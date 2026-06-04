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

package hu.bme.mit.theta.frontend.header

internal val atomicfunc_h =
  """
void* __atomic_load_n (void* *ptr, int memorder);
void __atomic_load (void* *ptr, void* *ret, int memorder);

void __atomic_store_n (void* *ptr, void* val, int memorder);
void __atomic_store (void* *ptr, void* *val, int memorder);

void* __atomic_exchange_n (void* *ptr, void* val, int memorder);
void __atomic_exchange (void* *ptr, void* *val, void* *ret, int memorder);

bool __atomic_compare_exchange_n (void* *ptr, void* *expected, void* desired, bool weak, int success_memorder, int failure_memorder);
bool __atomic_compare_exchange (void* *ptr, void* *expected, void* *desired, bool weak, int success_memorder, int failure_memorder);

void* __atomic_add_fetch (void* *ptr, void* val, int memorder);
void* __atomic_sub_fetch (void* *ptr, void* val, int memorder);
void* __atomic_and_fetch (void* *ptr, void* val, int memorder);
void* __atomic_xor_fetch (void* *ptr, void* val, int memorder);
void* __atomic_or_fetch (void* *ptr, void* val, int memorder);
void* __atomic_nand_fetch (void* *ptr, void* val, int memorder);

void* __atomic_fetch_add (void* *ptr, void* val, int memorder);
void* __atomic_fetch_sub (void* *ptr, void* val, int memorder);
void* __atomic_fetch_and (void* *ptr, void* val, int memorder);
void* __atomic_fetch_xor (void* *ptr, void* val, int memorder);
void* __atomic_fetch_or (void* *ptr, void* val, int memorder);
void* __atomic_fetch_nand (void* *ptr, void* val, int memorder);

bool __atomic_test_and_set (void *ptr, int memorder);

void __atomic_clear (bool *ptr, int memorder);

void __atomic_thread_fence (int memorder);
void __atomic_signal_fence (int memorder);

bool __atomic_always_lock_free (size_t size, void *ptr);
bool __atomic_is_lock_free (size_t size, void *ptr);
"""
    .trimIndent()
