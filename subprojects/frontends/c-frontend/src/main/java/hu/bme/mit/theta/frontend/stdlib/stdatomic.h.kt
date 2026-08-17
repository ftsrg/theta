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
package hu.bme.mit.theta.frontend.stdlib

/**
 * C11 `<stdatomic.h>`: the names, not the operations.
 *
 * The atomic types are ordinary `_Atomic` types and are declared as such -- that is the whole of
 * what they are. The *operations* (`atomic_load`, `atomic_fetch_add`, ...) are type-generic, which
 * C expresses with macros and this grammar cannot express at all, so they are not declared here:
 * `ExpressionVisitor` recognises them by name and builds the load, the store or the read-modify-
 * write directly, exactly as it does for the `__atomic_*` builtins they compile down to.
 *
 * `memory_order` is an ordinary int, and its constants are given values by `MacroExprs`. The order
 * itself constrains only what may be *reordered* around an access, and the analysis is sequentially
 * consistent -- it never reorders -- so honouring it would rule out nothing that is not ruled out
 * already.
 */
internal val stdatomic_h =
  """
typedef _Atomic _Bool atomic_bool;
typedef _Atomic char atomic_char;
typedef _Atomic signed char atomic_schar;
typedef _Atomic unsigned char atomic_uchar;
typedef _Atomic short atomic_short;
typedef _Atomic unsigned short atomic_ushort;
typedef _Atomic int atomic_int;
typedef _Atomic unsigned int atomic_uint;
typedef _Atomic long atomic_long;
typedef _Atomic unsigned long atomic_ulong;
typedef _Atomic long long atomic_llong;
typedef _Atomic unsigned long long atomic_ullong;
typedef _Atomic unsigned long atomic_size_t;
typedef _Atomic long atomic_ptrdiff_t;
typedef _Atomic long atomic_intptr_t;
typedef _Atomic unsigned long atomic_uintptr_t;
typedef _Atomic long atomic_intmax_t;
typedef _Atomic unsigned long atomic_uintmax_t;

typedef int memory_order;

typedef struct atomic_flag { _Atomic _Bool _Value; } atomic_flag;
"""
    .trimIndent()
