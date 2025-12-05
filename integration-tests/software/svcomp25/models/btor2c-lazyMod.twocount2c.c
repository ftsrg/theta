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
void reach_error() { __assert_fail("0", "twocount2c.c", 0, "reach_error"); }
void __VERIFIER_assert(int cond) { if (!(cond)) { ERROR: { reach_error(); abort(); } } }
void assume_abort_if_not(int cond) { if (!cond) { abort(); } }
int main() {
  // Defining sorts ...
  typedef unsigned char SORT_1;  // BV with 1 bits
  const SORT_1 mask_SORT_1 = (SORT_1)-1 >> (sizeof(SORT_1) * 8 - 1);
  const SORT_1 msb_SORT_1 = (SORT_1)1 << (1 - 1);
  typedef unsigned char SORT_2;  // BV with 2 bits
  const SORT_2 mask_SORT_2 = (SORT_2)-1 >> (sizeof(SORT_2) * 8 - 2);
  const SORT_2 msb_SORT_2 = (SORT_2)1 << (2 - 1);
  // Initializing constants ...
  const SORT_2 var_5 = 0;
  const SORT_2 var_10 = 1;
  const SORT_2 var_17 = mask_SORT_2;
  // Collecting input declarations ...
  SORT_1 input_3;
  SORT_1 input_4;
  // Collecting state declarations ...
  SORT_2 state_6 = __VERIFIER_nondet_uchar() & mask_SORT_2;
  SORT_2 state_7 = __VERIFIER_nondet_uchar() & mask_SORT_2;
  // Initializing states ...
  SORT_2 init_8_arg_1 = var_5;
  state_6 = init_8_arg_1;
  SORT_2 init_9_arg_1 = var_5;
  state_7 = init_9_arg_1;
  for (;;) {
    // Getting external input values ...
    input_3 = __VERIFIER_nondet_uchar();
    input_3 = input_3 & mask_SORT_1;
    input_4 = __VERIFIER_nondet_uchar();
    input_4 = input_4 & mask_SORT_1;
    // Assuming invariants ...
    SORT_1 var_22_arg_0 = input_3;
    SORT_1 var_22_arg_1 = input_4;
    SORT_1 var_22 = ~(var_22_arg_0 & var_22_arg_1);
    var_22 = var_22 & mask_SORT_1;
    SORT_1 constr_23_arg_0 = var_22;
    assume_abort_if_not(constr_23_arg_0);
    // Asserting properties ...
    SORT_2 var_18_arg_0 = state_6;
    SORT_2 var_18_arg_1 = var_17;
    SORT_1 var_18 = var_18_arg_0 == var_18_arg_1;
    SORT_2 var_19_arg_0 = state_7;
    SORT_2 var_19_arg_1 = var_17;
    SORT_1 var_19 = var_19_arg_0 == var_19_arg_1;
    SORT_1 var_20_arg_0 = var_18;
    SORT_1 var_20_arg_1 = var_19;
    SORT_1 var_20 = var_20_arg_0 & var_20_arg_1;
    var_20 = var_20 & mask_SORT_1;
    SORT_1 bad_21_arg_0 = var_20;
    __VERIFIER_assert(!(bad_21_arg_0));
    // Computing next states ...
    SORT_2 var_11_arg_0 = state_6;
    SORT_2 var_11_arg_1 = var_10;
    SORT_2 var_11 = var_11_arg_0 + var_11_arg_1;
    SORT_1 var_13_arg_0 = input_3;
    SORT_2 var_13_arg_1 = var_11;
    SORT_2 var_13_arg_2 = state_6;
    SORT_2 var_13 = var_13_arg_0 ? var_13_arg_1 : var_13_arg_2;
    var_13 = var_13 & mask_SORT_2;
    SORT_2 next_15_arg_1 = var_13;
    SORT_2 var_12_arg_0 = state_7;
    SORT_2 var_12_arg_1 = var_10;
    SORT_2 var_12 = var_12_arg_0 + var_12_arg_1;
    SORT_1 var_14_arg_0 = input_4;
    SORT_2 var_14_arg_1 = var_12;
    SORT_2 var_14_arg_2 = state_7;
    SORT_2 var_14 = var_14_arg_0 ? var_14_arg_1 : var_14_arg_2;
    var_14 = var_14 & mask_SORT_2;
    SORT_2 next_16_arg_1 = var_14;
    // Assigning next states ...
    state_6 = next_15_arg_1;
    state_7 = next_16_arg_1;
  }
  return 0;
}
