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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch7525_while.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
unsigned char var_1_1 = 32;
unsigned char var_1_7 = 128;
unsigned char var_1_8 = 64;
unsigned char var_1_9 = 100;
unsigned char var_1_10 = 1;
float var_1_11 = -0.6;
unsigned char var_1_12 = 1;
double var_1_13 = 999999999999999.2;
float var_1_14 = 50.25;
float var_1_15 = 15.5;
float var_1_16 = 128.5;
unsigned char var_1_17 = 0;
unsigned char last_1_var_1_17 = 0;
void initially(void) {
}
void step(void) {
 signed long int stepLocal_0 = (last_1_var_1_17 * last_1_var_1_17) * last_1_var_1_17;
 if (stepLocal_0 < ((((last_1_var_1_17) > (last_1_var_1_17)) ? (last_1_var_1_17) : (last_1_var_1_17)))) {
  var_1_1 = (var_1_7 - (((((var_1_8) < (var_1_9)) ? (var_1_8) : (var_1_9))) - var_1_10));
 } else {
  var_1_1 = var_1_8;
 }
 unsigned char stepLocal_1 = var_1_1;
 if (stepLocal_1 >= var_1_1) {
  var_1_17 = (((((var_1_7) < 0 ) ? -(var_1_7) : (var_1_7))) - (((((((var_1_9) > (var_1_10)) ? (var_1_9) : (var_1_10))) < 0 ) ? -((((var_1_9) > (var_1_10)) ? (var_1_9) : (var_1_10))) : ((((var_1_9) > (var_1_10)) ? (var_1_9) : (var_1_10))))));
 } else {
  var_1_17 = var_1_8;
 }
 if (var_1_12 || ((var_1_13 * 49.25) == 32.8)) {
  var_1_11 = (((((var_1_14 + var_1_15)) > (var_1_16)) ? ((var_1_14 + var_1_15)) : (var_1_16)));
 } else {
  var_1_11 = var_1_15;
 }
}
void updateVariables() {
 var_1_7 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_7 >= 127);
 assume_abort_if_not(var_1_7 <= 254);
 var_1_8 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_8 >= 63);
 assume_abort_if_not(var_1_8 <= 127);
 var_1_9 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_9 >= 63);
 assume_abort_if_not(var_1_9 <= 127);
 var_1_10 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_10 >= 0);
 assume_abort_if_not(var_1_10 <= 63);
 var_1_12 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_12 >= 0);
 assume_abort_if_not(var_1_12 <= 1);
 var_1_13 = __VERIFIER_nondet_double();
 assume_abort_if_not((var_1_13 >= -922337.2036854776000e+13F && var_1_13 <= -1.0e-20F) || (var_1_13 <= 9223372.036854776000e+12F && var_1_13 >= 1.0e-20F ));
 var_1_14 = __VERIFIER_nondet_float();
 assume_abort_if_not((var_1_14 >= -461168.6018427382800e+13F && var_1_14 <= -1.0e-20F) || (var_1_14 <= 4611686.018427382800e+12F && var_1_14 >= 1.0e-20F ));
 var_1_15 = __VERIFIER_nondet_float();
 assume_abort_if_not((var_1_15 >= -461168.6018427382800e+13F && var_1_15 <= -1.0e-20F) || (var_1_15 <= 4611686.018427382800e+12F && var_1_15 >= 1.0e-20F ));
 var_1_16 = __VERIFIER_nondet_float();
 assume_abort_if_not((var_1_16 >= -922337.2036854765600e+13F && var_1_16 <= -1.0e-20F) || (var_1_16 <= 9223372.036854765600e+12F && var_1_16 >= 1.0e-20F ));
}
void updateLastVariables() {
 last_1_var_1_17 = var_1_17;
}
int property() {
 return (((((last_1_var_1_17 * last_1_var_1_17) * last_1_var_1_17) < ((((last_1_var_1_17) > (last_1_var_1_17)) ? (last_1_var_1_17) : (last_1_var_1_17)))) ? (var_1_1 == ((unsigned char) (var_1_7 - (((((var_1_8) < (var_1_9)) ? (var_1_8) : (var_1_9))) - var_1_10)))) : (var_1_1 == ((unsigned char) var_1_8))) && ((var_1_12 || ((var_1_13 * 49.25) == 32.8)) ? (var_1_11 == ((float) (((((var_1_14 + var_1_15)) > (var_1_16)) ? ((var_1_14 + var_1_15)) : (var_1_16))))) : (var_1_11 == ((float) var_1_15)))) && ((var_1_1 >= var_1_1) ? (var_1_17 == ((unsigned char) (((((var_1_7) < 0 ) ? -(var_1_7) : (var_1_7))) - (((((((var_1_9) > (var_1_10)) ? (var_1_9) : (var_1_10))) < 0 ) ? -((((var_1_9) > (var_1_10)) ? (var_1_9) : (var_1_10))) : ((((var_1_9) > (var_1_10)) ? (var_1_9) : (var_1_10)))))))) : (var_1_17 == ((unsigned char) var_1_8)))
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
