// This file is part of the SV-Benchmarks collection of verification tasks:
// https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks
//
// SPDX-FileCopyrightText: 2022 Jana (Philipp) Berger
//
// SPDX-License-Identifier: GPL-3.0-or-later

extern unsigned long __VERIFIER_nondet_ulong();
extern long __VERIFIER_nondet_long();
extern unsigned char __VERIFIER_nondet_uchar();
extern char __VERIFIER_nondet_char();
extern unsigned short __VERIFIER_nondet_ushort();
extern short __VERIFIER_nondet_short();
extern float __VERIFIER_nondet_float();
extern double __VERIFIER_nondet_double();
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch74Amount10.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
signed long int var_1_1 = 32;
unsigned long int var_1_2 = 4;
signed long int var_1_3 = 1767209045;
signed long int var_1_4 = 256;
signed long int var_1_5 = 100000;
signed long int var_1_6 = 32;
signed long int var_1_7 = 128;
unsigned char var_1_8 = 0;
void initially(void) {
}
void step(void) {
 if (5u < (32u % var_1_2)) {
  var_1_1 = ((((((var_1_3 - var_1_4) - var_1_5)) > ((var_1_6 - var_1_7))) ? (((var_1_3 - var_1_4) - var_1_5)) : ((var_1_6 - var_1_7))));
 } else {
  if (var_1_8) {
   var_1_1 = var_1_6;
  } else {
   var_1_1 = var_1_7;
  }
 }
}
void updateVariables() {
 var_1_2 = __VERIFIER_nondet_ulong();
 assume_abort_if_not(var_1_2 >= 0);
 assume_abort_if_not(var_1_2 <= 4294967295);
 assume_abort_if_not(var_1_2 != 0);
 var_1_3 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_3 >= 1073741822);
 assume_abort_if_not(var_1_3 <= 2147483646);
 var_1_4 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_4 >= 0);
 assume_abort_if_not(var_1_4 <= 1073741823);
 var_1_5 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_5 >= 0);
 assume_abort_if_not(var_1_5 <= 2147483646);
 var_1_6 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_6 >= -1);
 assume_abort_if_not(var_1_6 <= 2147483646);
 var_1_7 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_7 >= 0);
 assume_abort_if_not(var_1_7 <= 2147483646);
 var_1_8 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_8 >= 0);
 assume_abort_if_not(var_1_8 <= 1);
}
void updateLastVariables() {
}
int property() {
 return (5u < (32u % var_1_2)) ? (var_1_1 == ((signed long int) ((((((var_1_3 - var_1_4) - var_1_5)) > ((var_1_6 - var_1_7))) ? (((var_1_3 - var_1_4) - var_1_5)) : ((var_1_6 - var_1_7)))))) : (var_1_8 ? (var_1_1 == ((signed long int) var_1_6)) : (var_1_1 == ((signed long int) var_1_7)))
;
}
int main(void) {
 isInitial = 1;
 initially();
 while (1) {
  updateLastVariables();
  updateVariables();
  step();
  __VERIFIER_assert(property());
  isInitial = 0;
 }
 return 0;
}
