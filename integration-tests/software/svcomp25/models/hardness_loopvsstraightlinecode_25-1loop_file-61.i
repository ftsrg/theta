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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch6125_1loop.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
unsigned char var_1_1 = 0;
float var_1_2 = 128.6;
float var_1_3 = 49.4;
unsigned char var_1_4 = 0;
unsigned char var_1_5 = 0;
unsigned char var_1_6 = 0;
unsigned char var_1_7 = 8;
unsigned char var_1_8 = 128;
unsigned char var_1_9 = 64;
signed short int var_1_10 = 5;
void initially(void) {
}
void step(void) {
 if (var_1_2 < var_1_3) {
  var_1_1 = (var_1_4 || var_1_5);
 } else {
  if (var_1_3 >= var_1_2) {
   var_1_1 = var_1_5;
  } else {
   var_1_1 = var_1_6;
  }
 }
 if (var_1_6) {
  if (var_1_3 != 15.8f) {
   var_1_7 = (var_1_8 - var_1_9);
  } else {
   var_1_7 = ((((var_1_8) > (var_1_9)) ? (var_1_8) : (var_1_9)));
  }
 } else {
  var_1_7 = var_1_8;
 }
 signed long int stepLocal_0 = (var_1_9 / 32) << var_1_8;
 if (! (var_1_3 < var_1_2)) {
  if (stepLocal_0 == var_1_7) {
   var_1_10 = (var_1_7 - var_1_8);
  }
 }
}
void updateVariables() {
 var_1_2 = __VERIFIER_nondet_float();
 assume_abort_if_not((var_1_2 >= -922337.2036854776000e+13F && var_1_2 <= -1.0e-20F) || (var_1_2 <= 9223372.036854776000e+12F && var_1_2 >= 1.0e-20F ));
 var_1_3 = __VERIFIER_nondet_float();
 assume_abort_if_not((var_1_3 >= -922337.2036854776000e+13F && var_1_3 <= -1.0e-20F) || (var_1_3 <= 9223372.036854776000e+12F && var_1_3 >= 1.0e-20F ));
 var_1_4 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_4 >= 0);
 assume_abort_if_not(var_1_4 <= 0);
 var_1_5 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_5 >= 0);
 assume_abort_if_not(var_1_5 <= 0);
 var_1_6 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_6 >= 1);
 assume_abort_if_not(var_1_6 <= 1);
 var_1_8 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_8 >= 127);
 assume_abort_if_not(var_1_8 <= 254);
 var_1_9 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_9 >= 0);
 assume_abort_if_not(var_1_9 <= 127);
}
void updateLastVariables() {
}
int property() {
 return (((var_1_2 < var_1_3) ? (var_1_1 == ((unsigned char) (var_1_4 || var_1_5))) : ((var_1_3 >= var_1_2) ? (var_1_1 == ((unsigned char) var_1_5)) : (var_1_1 == ((unsigned char) var_1_6)))) && (var_1_6 ? ((var_1_3 != 15.8f) ? (var_1_7 == ((unsigned char) (var_1_8 - var_1_9))) : (var_1_7 == ((unsigned char) ((((var_1_8) > (var_1_9)) ? (var_1_8) : (var_1_9)))))) : (var_1_7 == ((unsigned char) var_1_8)))) && ((! (var_1_3 < var_1_2)) ? ((((var_1_9 / 32) << var_1_8) == var_1_7) ? (var_1_10 == ((signed short int) (var_1_7 - var_1_8))) : 1) : 1)
;
}
int main(void) {
 isInitial = 1;
 initially();
 int k_loop;
 for (k_loop = 0; k_loop < 1; k_loop++) {
  updateLastVariables();
  updateVariables();
  step();
  __VERIFIER_assert(property());
  isInitial = 0;
 }
 return 0;
}
