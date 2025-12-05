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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch21Amount10.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
signed long int var_1_1 = -16;
signed long int var_1_6 = 10;
unsigned char var_1_8 = 0;
unsigned char var_1_9 = 4;
float var_1_10 = 15.5;
float var_1_11 = 99.125;
signed short int var_1_12 = 2;
signed long int last_1_var_1_1 = -16;
void initially(void) {
}
void step(void) {
 var_1_8 = var_1_9;
 var_1_10 = var_1_11;
 var_1_12 = var_1_9;
 signed long int stepLocal_0 = var_1_8 & (var_1_12 * var_1_8);
 if (stepLocal_0 < (last_1_var_1_1 / var_1_6)) {
  var_1_1 = (var_1_8 + 256);
 }
}
void updateVariables() {
 var_1_6 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_6 >= -2147483648);
 assume_abort_if_not(var_1_6 <= 2147483647);
 assume_abort_if_not(var_1_6 != 0);
 var_1_9 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_9 >= 0);
 assume_abort_if_not(var_1_9 <= 254);
 var_1_11 = __VERIFIER_nondet_float();
 assume_abort_if_not((var_1_11 >= -922337.2036854765600e+13F && var_1_11 <= -1.0e-20F) || (var_1_11 <= 9223372.036854765600e+12F && var_1_11 >= 1.0e-20F ));
}
void updateLastVariables() {
 last_1_var_1_1 = var_1_1;
}
int property() {
 return (((((var_1_8 & (var_1_12 * var_1_8)) < (last_1_var_1_1 / var_1_6)) ? (var_1_1 == ((signed long int) (var_1_8 + 256))) : 1) && (var_1_8 == ((unsigned char) var_1_9))) && (var_1_10 == ((float) var_1_11))) && (var_1_12 == ((signed short int) var_1_9))
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
