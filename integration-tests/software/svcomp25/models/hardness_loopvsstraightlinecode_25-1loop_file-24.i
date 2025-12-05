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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch2425_1loop.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
signed char var_1_1 = 32;
unsigned char var_1_2 = 0;
float var_1_3 = 127.1;
signed char var_1_4 = 16;
signed char var_1_5 = 4;
unsigned char var_1_6 = 8;
float var_1_7 = 1000000.6;
unsigned char var_1_8 = 64;
unsigned char var_1_9 = 64;
unsigned char var_1_10 = 128;
unsigned char var_1_11 = 32;
float var_1_12 = 16.8;
void initially(void) {
}
void step(void) {
 if (var_1_2 || (64.75f < var_1_3)) {
  if (var_1_2) {
   var_1_1 = (var_1_4 - var_1_5);
  } else {
   var_1_1 = var_1_4;
  }
 } else {
  var_1_1 = var_1_5;
 }
 if (var_1_3 <= var_1_7) {
  var_1_6 = ((((((var_1_8 + var_1_9)) > (((((var_1_10) > (200)) ? (var_1_10) : (200))))) ? ((var_1_8 + var_1_9)) : (((((var_1_10) > (200)) ? (var_1_10) : (200)))))) - var_1_5);
 } else {
  var_1_6 = var_1_10;
 }
 if (((((var_1_6) > (var_1_8)) ? (var_1_6) : (var_1_8))) <= var_1_10) {
  if (var_1_3 == (var_1_7 + var_1_12)) {
   var_1_11 = (var_1_9 + var_1_5);
  } else {
   var_1_11 = var_1_9;
  }
 }
}
void updateVariables() {
 var_1_2 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_2 >= 0);
 assume_abort_if_not(var_1_2 <= 1);
 var_1_3 = __VERIFIER_nondet_float();
 assume_abort_if_not((var_1_3 >= -922337.2036854776000e+13F && var_1_3 <= -1.0e-20F) || (var_1_3 <= 9223372.036854776000e+12F && var_1_3 >= 1.0e-20F ));
 var_1_4 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_4 >= -1);
 assume_abort_if_not(var_1_4 <= 126);
 var_1_5 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_5 >= 0);
 assume_abort_if_not(var_1_5 <= 126);
 var_1_7 = __VERIFIER_nondet_float();
 assume_abort_if_not((var_1_7 >= -922337.2036854776000e+13F && var_1_7 <= -1.0e-20F) || (var_1_7 <= 9223372.036854776000e+12F && var_1_7 >= 1.0e-20F ));
 var_1_8 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_8 >= 63);
 assume_abort_if_not(var_1_8 <= 127);
 var_1_9 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_9 >= 64);
 assume_abort_if_not(var_1_9 <= 127);
 var_1_10 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_10 >= 127);
 assume_abort_if_not(var_1_10 <= 254);
 var_1_12 = __VERIFIER_nondet_float();
 assume_abort_if_not((var_1_12 >= -922337.2036854776000e+13F && var_1_12 <= -1.0e-20F) || (var_1_12 <= 9223372.036854776000e+12F && var_1_12 >= 1.0e-20F ));
}
void updateLastVariables() {
}
int property() {
 return (((var_1_2 || (64.75f < var_1_3)) ? (var_1_2 ? (var_1_1 == ((signed char) (var_1_4 - var_1_5))) : (var_1_1 == ((signed char) var_1_4))) : (var_1_1 == ((signed char) var_1_5))) && ((var_1_3 <= var_1_7) ? (var_1_6 == ((unsigned char) ((((((var_1_8 + var_1_9)) > (((((var_1_10) > (200)) ? (var_1_10) : (200))))) ? ((var_1_8 + var_1_9)) : (((((var_1_10) > (200)) ? (var_1_10) : (200)))))) - var_1_5))) : (var_1_6 == ((unsigned char) var_1_10)))) && ((((((var_1_6) > (var_1_8)) ? (var_1_6) : (var_1_8))) <= var_1_10) ? ((var_1_3 == (var_1_7 + var_1_12)) ? (var_1_11 == ((unsigned char) (var_1_9 + var_1_5))) : (var_1_11 == ((unsigned char) var_1_9))) : 1)
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
