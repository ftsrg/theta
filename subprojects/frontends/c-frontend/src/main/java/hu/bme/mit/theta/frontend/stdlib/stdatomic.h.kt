/*
 *  Copyright 2025 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.frontend.stdlib

internal val stdatomic_h =
  """
typedef enum {
  memory_order_relaxed,
  memory_order_consume,
  memory_order_acquire,
  memory_order_release,
  memory_order_acq_rel,
  memory_order_seq_cst
} memory_order;

typedef _Bool atomic_bool;
typedef char atomic_char;
typedef signed char atomic_schar;
typedef unsigned char atomic_uchar;
typedef short atomic_short;
typedef unsigned short atomic_ushort;
typedef int atomic_int;
typedef unsigned int atomic_uint;
typedef long atomic_long;
typedef unsigned long atomic_ulong;
typedef long long atomic_llong;
typedef unsigned long long atomic_ullong;
typedef long atomic_intptr_t;
typedef unsigned long atomic_uintptr_t;
typedef unsigned long atomic_size_t;
typedef long atomic_ptrdiff_t;
typedef long atomic_intmax_t;
typedef unsigned long atomic_uintmax_t;

typedef struct {
  int __flag;
} atomic_flag;

#define ATOMIC_FLAG_INIT \
  { 0 }
#define ATOMIC_VAR_INIT(value) (value)

#define atomic_init(obj, value) (*(obj) = (value))
#define atomic_is_lock_free(obj) 1

#define atomic_load_explicit(obj, order) __atomic_load_n(obj, order)
#define atomic_load(obj) atomic_load_explicit(obj, memory_order_seq_cst)

#define atomic_store_explicit(obj, value, order) __atomic_store_n(obj, value, order)
#define atomic_store(obj, value) atomic_store_explicit(obj, value, memory_order_seq_cst)

#define atomic_exchange_explicit(obj, value, order) __atomic_exchange_n(obj, value, order)
#define atomic_exchange(obj, value) atomic_exchange_explicit(obj, value, memory_order_seq_cst)

#define atomic_fetch_add_explicit(obj, value, order) __atomic_fetch_add(obj, value, order)
#define atomic_fetch_add(obj, value) atomic_fetch_add_explicit(obj, value, memory_order_seq_cst)

#define atomic_fetch_sub_explicit(obj, value, order) __atomic_fetch_sub(obj, value, order)
#define atomic_fetch_sub(obj, value) atomic_fetch_sub_explicit(obj, value, memory_order_seq_cst)

#define atomic_fetch_or_explicit(obj, value, order) __atomic_fetch_or(obj, value, order)
#define atomic_fetch_or(obj, value) atomic_fetch_or_explicit(obj, value, memory_order_seq_cst)

#define atomic_fetch_xor_explicit(obj, value, order) __atomic_fetch_xor(obj, value, order)
#define atomic_fetch_xor(obj, value) atomic_fetch_xor_explicit(obj, value, memory_order_seq_cst)

#define atomic_fetch_and_explicit(obj, value, order) __atomic_fetch_and(obj, value, order)
#define atomic_fetch_and(obj, value) atomic_fetch_and_explicit(obj, value, memory_order_seq_cst)

#define atomic_compare_exchange_strong_explicit(obj, expected, desired, success, failure) \
  __atomic_compare_exchange_n(obj, expected, desired, 0, success, failure)
#define atomic_compare_exchange_strong(obj, expected, desired) \
  atomic_compare_exchange_strong_explicit(obj, expected, desired, memory_order_seq_cst, memory_order_seq_cst)

#define atomic_compare_exchange_weak_explicit(obj, expected, desired, success, failure) \
  __atomic_compare_exchange_n(obj, expected, desired, 1, success, failure)
#define atomic_compare_exchange_weak(obj, expected, desired) \
  atomic_compare_exchange_weak_explicit(obj, expected, desired, memory_order_seq_cst, memory_order_seq_cst)

#define atomic_flag_test_and_set_explicit(obj, order) __atomic_test_and_set(&(obj)->__flag, order)
#define atomic_flag_test_and_set(obj) atomic_flag_test_and_set_explicit(obj, memory_order_seq_cst)

#define atomic_flag_clear_explicit(obj, order) __atomic_clear(&(obj)->__flag, order)
#define atomic_flag_clear(obj) atomic_flag_clear_explicit(obj, memory_order_seq_cst)

#define atomic_thread_fence(order) __atomic_thread_fence(order)
#define atomic_signal_fence(order) __atomic_signal_fence(order)
"""
    .trimIndent()
