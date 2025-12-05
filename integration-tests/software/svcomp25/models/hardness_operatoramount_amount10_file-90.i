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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch90Amount10.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
signed long int var_1_1 = -16;
signed long int var_1_3 = 16;
signed long int var_1_4 = 0;
signed long int var_1_5 = 1732512216;
signed long int var_1_6 = 10;
signed long int last_1_var_1_1 = -16;
void initially(void) {
}
void step(void) {
 signed long int stepLocal_1 = var_1_4 * var_1_6;
 unsigned long int stepLocal_0 = 16u;
 if (stepLocal_0 < last_1_var_1_1) {
  var_1_1 = ((var_1_3 + var_1_4) - (var_1_5 - var_1_6));
 } else {
  if (var_1_3 <= stepLocal_1) {
   var_1_1 = var_1_6;
  } else {
   var_1_1 = -4;
  }
 }
}
void updateVariables() {
 var_1_3 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_3 >= 0);
 assume_abort_if_not(var_1_3 <= 1073741823);
 var_1_4 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_4 >= 0);
 assume_abort_if_not(var_1_4 <= 1073741823);
 var_1_5 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_5 >= 1073741823);
 assume_abort_if_not(var_1_5 <= 2147483646);
 var_1_6 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_6 >= 0);
 assume_abort_if_not(var_1_6 <= 1073741823);
}
void updateLastVariables() {
 last_1_var_1_1 = var_1_1;
}
int property() {
 return (16u < last_1_var_1_1) ? (var_1_1 == ((signed long int) ((var_1_3 + var_1_4) - (var_1_5 - var_1_6)))) : ((var_1_3 <= (var_1_4 * var_1_6)) ? (var_1_1 == ((signed long int) var_1_6)) : (var_1_1 == ((signed long int) -4)))
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
