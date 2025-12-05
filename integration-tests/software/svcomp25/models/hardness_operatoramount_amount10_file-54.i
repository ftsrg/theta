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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch54Amount10.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
float var_1_1 = 999.25;
float var_1_5 = 63.875;
float var_1_6 = 25.05;
signed long int var_1_7 = -4;
float var_1_8 = 25.2;
signed long int var_1_9 = 2;
signed long int var_1_10 = 256;
signed long int last_1_var_1_7 = -4;
void initially(void) {
}
void step(void) {
 signed long int stepLocal_0 = last_1_var_1_7;
 if (last_1_var_1_7 < stepLocal_0) {
  var_1_1 = (var_1_5 - var_1_6);
 }
 if ((((((var_1_5 / var_1_8)) > (var_1_6)) ? ((var_1_5 / var_1_8)) : (var_1_6))) == var_1_1) {
  var_1_7 = (var_1_9 + var_1_10);
 } else {
  var_1_7 = 50;
 }
}
void updateVariables() {
 var_1_5 = __VERIFIER_nondet_float();
 assume_abort_if_not((var_1_5 >= 0.0F && var_1_5 <= -1.0e-20F) || (var_1_5 <= 9223372.036854765600e+12F && var_1_5 >= 1.0e-20F ));
 var_1_6 = __VERIFIER_nondet_float();
 assume_abort_if_not((var_1_6 >= 0.0F && var_1_6 <= -1.0e-20F) || (var_1_6 <= 9223372.036854765600e+12F && var_1_6 >= 1.0e-20F ));
 var_1_8 = __VERIFIER_nondet_float();
 assume_abort_if_not((var_1_8 >= -922337.2036854776000e+13F && var_1_8 <= -1.0e-20F) || (var_1_8 <= 9223372.036854776000e+12F && var_1_8 >= 1.0e-20F ));
 assume_abort_if_not(var_1_8 != 0.0F);
 var_1_9 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_9 >= -1073741823);
 assume_abort_if_not(var_1_9 <= 1073741823);
 var_1_10 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_10 >= -1073741823);
 assume_abort_if_not(var_1_10 <= 1073741823);
}
void updateLastVariables() {
 last_1_var_1_7 = var_1_7;
}
int property() {
 return ((last_1_var_1_7 < last_1_var_1_7) ? (var_1_1 == ((float) (var_1_5 - var_1_6))) : 1) && (((((((var_1_5 / var_1_8)) > (var_1_6)) ? ((var_1_5 / var_1_8)) : (var_1_6))) == var_1_1) ? (var_1_7 == ((signed long int) (var_1_9 + var_1_10))) : (var_1_7 == ((signed long int) 50)))
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
