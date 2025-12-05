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
// ; int i = 1, factorial = 1;
// ; assert (i <= 2 || !(factorial & 1));
// ; for (;;) {
// ;   factorial *= i;
// ;   i++;
// ;   assert (i <= 2 || !(factorial & 1));
// ; }
extern unsigned char __VERIFIER_nondet_uchar();
extern unsigned short __VERIFIER_nondet_ushort();
extern unsigned int __VERIFIER_nondet_uint();
extern unsigned long __VERIFIER_nondet_ulong();
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *);
void reach_error() { __assert_fail("0", "factorial4even.c", 0, "reach_error"); }
void __VERIFIER_assert(int cond) { if (!(cond)) { ERROR: { reach_error(); abort(); } } }
void assume_abort_if_not(int cond) { if (!cond) { abort(); } }
int main() {
  // Defining sorts ...
  typedef unsigned char SORT_1;  // BV with 4 bits
  const SORT_1 mask_SORT_1 = (SORT_1)-1 >> (sizeof(SORT_1) * 8 - 4);
  const SORT_1 msb_SORT_1 = (SORT_1)1 << (4 - 1);
  typedef unsigned char SORT_12;  // BV with 1 bits
  const SORT_12 mask_SORT_12 = (SORT_12)-1 >> (sizeof(SORT_12) * 8 - 1);
  const SORT_12 msb_SORT_12 = (SORT_12)1 << (1 - 1);
  // Initializing constants ...
  const SORT_1 var_2 = 1;
  const SORT_1 var_11 = mask_SORT_1;
  const SORT_1 var_16 = 3;
  // Collecting input declarations ...
  // Collecting state declarations ...
  SORT_1 state_3 = __VERIFIER_nondet_uchar() & mask_SORT_1;
  SORT_1 state_4 = __VERIFIER_nondet_uchar() & mask_SORT_1;
  // Initializing states ...
  SORT_1 init_5_arg_1 = var_2;
  state_3 = init_5_arg_1;
  SORT_1 init_6_arg_1 = var_2;
  state_4 = init_6_arg_1;
  for (;;) {
    // Getting external input values ...
    // Assuming invariants ...
    // Asserting properties ...
    SORT_1 var_13_arg_0 = state_4;
    SORT_1 var_13_arg_1 = var_11;
    SORT_12 var_13 = var_13_arg_0 == var_13_arg_1;
    SORT_12 bad_14_arg_0 = var_13;
    __VERIFIER_assert(!(bad_14_arg_0));
    SORT_1 var_17_arg_0 = state_4;
    SORT_1 var_17_arg_1 = var_16;
    SORT_12 var_17 = var_17_arg_0 > var_17_arg_1;
    SORT_1 var_15_arg_0 = state_3;
    SORT_12 var_15 = var_15_arg_0 >> 0;
    SORT_12 var_18_arg_0 = var_17;
    SORT_12 var_18_arg_1 = var_15;
    SORT_12 var_18 = var_18_arg_0 & var_18_arg_1;
    var_18 = var_18 & mask_SORT_12;
    SORT_12 bad_19_arg_0 = var_18;
    __VERIFIER_assert(!(bad_19_arg_0));
    // Computing next states ...
    SORT_1 var_7_arg_0 = state_4;
    SORT_1 var_7_arg_1 = var_2;
    SORT_1 var_7 = var_7_arg_0 + var_7_arg_1;
    var_7 = var_7 & mask_SORT_1;
    SORT_1 next_9_arg_1 = var_7;
    SORT_1 var_8_arg_0 = state_3;
    SORT_1 var_8_arg_1 = state_4;
    SORT_1 var_8 = var_8_arg_0 * var_8_arg_1;
    SORT_1 next_10_arg_1 = var_8;
    // Assigning next states ...
    state_4 = next_9_arg_1;
    state_3 = next_10_arg_1;
  }
  return 0;
}
