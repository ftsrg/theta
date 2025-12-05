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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch5225_while.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
signed short int var_1_1 = -4;
double var_1_2 = 255.6;
unsigned char var_1_5 = 1;
unsigned char var_1_6 = 0;
unsigned char var_1_7 = 0;
unsigned char var_1_8 = 0;
unsigned char var_1_9 = 8;
double var_1_10 = 255.2;
unsigned char var_1_11 = 64;
unsigned char var_1_12 = 100;
unsigned char var_1_13 = 32;
unsigned char var_1_14 = 64;
unsigned char var_1_15 = 0;
void initially(void) {
}
void step(void) {
 if ((- var_1_2) <= var_1_10) {
  var_1_9 = ((((((var_1_11 + var_1_12) - var_1_13)) < ((var_1_14 + var_1_15))) ? (((var_1_11 + var_1_12) - var_1_13)) : ((var_1_14 + var_1_15))));
 } else {
  var_1_9 = var_1_12;
 }
 if (var_1_2 < 63.75) {
  var_1_1 = (10 - var_1_9);
 } else {
  var_1_1 = (4 + var_1_9);
 }
 signed long int stepLocal_0 = (var_1_9 / -256) * 32;
 if (var_1_9 > stepLocal_0) {
  if (var_1_6) {
   var_1_5 = (! (var_1_7 && (! var_1_8)));
  } else {
   var_1_5 = var_1_7;
  }
 } else {
  var_1_5 = var_1_7;
 }
}
void updateVariables() {
 var_1_2 = __VERIFIER_nondet_double();
 assume_abort_if_not((var_1_2 >= -922337.2036854776000e+13F && var_1_2 <= -1.0e-20F) || (var_1_2 <= 9223372.036854776000e+12F && var_1_2 >= 1.0e-20F ));
 var_1_6 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_6 >= 0);
 assume_abort_if_not(var_1_6 <= 1);
 var_1_7 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_7 >= 1);
 assume_abort_if_not(var_1_7 <= 1);
 var_1_8 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_8 >= 0);
 assume_abort_if_not(var_1_8 <= 0);
 var_1_10 = __VERIFIER_nondet_double();
 assume_abort_if_not((var_1_10 >= -922337.2036854776000e+13F && var_1_10 <= -1.0e-20F) || (var_1_10 <= 9223372.036854776000e+12F && var_1_10 >= 1.0e-20F ));
 var_1_11 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_11 >= 63);
 assume_abort_if_not(var_1_11 <= 127);
 var_1_12 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_12 >= 64);
 assume_abort_if_not(var_1_12 <= 127);
 var_1_13 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_13 >= 0);
 assume_abort_if_not(var_1_13 <= 127);
 var_1_14 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_14 >= 0);
 assume_abort_if_not(var_1_14 <= 127);
 var_1_15 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_15 >= 0);
 assume_abort_if_not(var_1_15 <= 127);
}
void updateLastVariables() {
}
int property() {
 return (((var_1_2 < 63.75) ? (var_1_1 == ((signed short int) (10 - var_1_9))) : (var_1_1 == ((signed short int) (4 + var_1_9)))) && ((var_1_9 > ((var_1_9 / -256) * 32)) ? (var_1_6 ? (var_1_5 == ((unsigned char) (! (var_1_7 && (! var_1_8))))) : (var_1_5 == ((unsigned char) var_1_7))) : (var_1_5 == ((unsigned char) var_1_7)))) && (((- var_1_2) <= var_1_10) ? (var_1_9 == ((unsigned char) ((((((var_1_11 + var_1_12) - var_1_13)) < ((var_1_14 + var_1_15))) ? (((var_1_11 + var_1_12) - var_1_13)) : ((var_1_14 + var_1_15)))))) : (var_1_9 == ((unsigned char) var_1_12)))
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
