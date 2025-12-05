// This file is part of the SV-Benchmarks collection of verification tasks:
// https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks
//
// SPDX-FileCopyrightText: 2012 - 2018 Armin Biere
// SPDX-FileCopyrightText: 2013 - 2018 Mathias Preiner
// SPDX-FileCopyrightText: 2015 - 2018 Aina Niemetz
// SPDX-FileCopyrightText: 2022 The SV-Benchmarks Community
//
// SPDX-License-Identifier: MIT

// This C program is converted from Btor2 by Btor2C version sha1:a0fa249
//   with arguments: { architecture=64, lazy_modulo=true, use_memmove=false, unroll_inner_loops=false, shortest_type=true, diff_type=true, decimal_constant=true, zero_init=false, sra_extend_sign=true }
// Comments from the original Btor2 file:
// ; source: https://github.com/Boolector/btor2tools/tree/b8456dda4780789e882f5791eb486f295ade4da4/examples/btorsim
extern unsigned char __VERIFIER_nondet_uchar();
extern unsigned short __VERIFIER_nondet_ushort();
extern unsigned int __VERIFIER_nondet_uint();
extern unsigned long __VERIFIER_nondet_ulong();
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "count2.c", 0, "reach_error"); }
void __VERIFIER_assert(int cond) { if (!(cond)) { ERROR: { reach_error(); abort(); } } }
void assume_abort_if_not(int cond) { if (!cond) { abort(); } }
int main() {
  // Defining sorts ...
  typedef unsigned char SORT_1;  // BV with 3 bits
  const SORT_1 mask_SORT_1 = (SORT_1)-1 >> (sizeof(SORT_1) * 8 - 3);
  const SORT_1 msb_SORT_1 = (SORT_1)1 << (3 - 1);
  typedef unsigned char SORT_9;  // BV with 1 bits
  const SORT_9 mask_SORT_9 = (SORT_9)-1 >> (sizeof(SORT_9) * 8 - 1);
  const SORT_9 msb_SORT_9 = (SORT_9)1 << (1 - 1);
  // Initializing constants ...
  const SORT_1 var_2 = 0;
  const SORT_1 var_5 = 1;
  const SORT_1 var_8 = mask_SORT_1;
  // Collecting input declarations ...
  // Collecting state declarations ...
  SORT_1 state_3 = __VERIFIER_nondet_uchar() & mask_SORT_1;
  // Initializing states ...
  SORT_1 init_4_arg_1 = var_2;
  state_3 = init_4_arg_1;
  for (;;) {
    // Getting external input values ...
    // Assuming invariants ...
    // Asserting properties ...
    SORT_1 var_10_arg_0 = state_3;
    SORT_1 var_10_arg_1 = var_8;
    SORT_9 var_10 = var_10_arg_0 == var_10_arg_1;
    SORT_9 bad_11_arg_0 = var_10;
    __VERIFIER_assert(!(bad_11_arg_0));
    // Computing next states ...
    SORT_1 var_6_arg_0 = state_3;
    SORT_1 var_6_arg_1 = var_5;
    SORT_1 var_6 = var_6_arg_0 + var_6_arg_1;
    var_6 = var_6 & mask_SORT_1;
    SORT_1 next_7_arg_1 = var_6;
    // Assigning next states ...
    state_3 = next_7_arg_1;
  }
  return 0;
}
