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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch42Amount10.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
signed long int var_1_1 = 5;
signed char var_1_7 = 32;
signed char var_1_8 = 16;
signed char var_1_9 = 32;
float var_1_10 = 127.725;
float var_1_11 = 2.2;
void initially(void) {
}
void step(void) {
 var_1_7 = var_1_8;
 var_1_9 = var_1_8;
 var_1_10 = var_1_11;
 if ((var_1_10 * var_1_10) > var_1_10) {
  var_1_1 = (var_1_7 + var_1_7);
 } else {
  var_1_1 = ((((var_1_7) > (5)) ? (var_1_7) : (5)));
 }
}
void updateVariables() {
 var_1_8 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_8 >= -127);
 assume_abort_if_not(var_1_8 <= 126);
 var_1_11 = __VERIFIER_nondet_float();
 assume_abort_if_not((var_1_11 >= -922337.2036854765600e+13F && var_1_11 <= -1.0e-20F) || (var_1_11 <= 9223372.036854765600e+12F && var_1_11 >= 1.0e-20F ));
}
void updateLastVariables() {
}
int property() {
 return (((((var_1_10 * var_1_10) > var_1_10) ? (var_1_1 == ((signed long int) (var_1_7 + var_1_7))) : (var_1_1 == ((signed long int) ((((var_1_7) > (5)) ? (var_1_7) : (5)))))) && (var_1_7 == ((signed char) var_1_8))) && (var_1_9 == ((signed char) var_1_8))) && (var_1_10 == ((float) var_1_11))
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
