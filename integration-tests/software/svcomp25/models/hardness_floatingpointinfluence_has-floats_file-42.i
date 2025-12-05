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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch42has_floats.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
signed long int var_1_1 = -1;
unsigned char var_1_8 = 5;
unsigned char var_1_9 = 4;
float var_1_10 = 16.5;
float var_1_11 = 127.25;
unsigned char var_1_12 = 1;
unsigned char var_1_13 = 0;
unsigned char var_1_15 = 0;
unsigned char var_1_16 = 0;
unsigned char var_1_17 = 0;
unsigned char var_1_18 = 0;
void initially(void) {
}
void step(void) {
 var_1_8 = (var_1_9 + 100);
 var_1_10 = ((((var_1_11) < (64.15f)) ? (var_1_11) : (64.15f)));
 if (var_1_8 > var_1_8) {
  var_1_1 = (((((var_1_8) < (var_1_8)) ? (var_1_8) : (var_1_8))) - 10);
 } else {
  var_1_1 = (((((var_1_8 - var_1_8)) > ((var_1_8 - var_1_8))) ? ((var_1_8 - var_1_8)) : ((var_1_8 - var_1_8))));
 }
 if (var_1_11 <= var_1_10) {
  if (var_1_1 != var_1_8) {
   var_1_17 = var_1_18;
  }
 } else {
  if (var_1_8 <= 1000000) {
   var_1_17 = 0;
  } else {
   var_1_17 = 0;
  }
 }
 if ((- var_1_10) > var_1_11) {
  var_1_12 = (var_1_13 || (var_1_17 && (var_1_15 || var_1_16)));
 } else {
  var_1_12 = ((var_1_1 <= var_1_9) && var_1_16);
 }
}
void updateVariables() {
 var_1_9 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_9 >= 0);
 assume_abort_if_not(var_1_9 <= 127);
 var_1_11 = __VERIFIER_nondet_float();
 assume_abort_if_not((var_1_11 >= -922337.2036854765600e+13F && var_1_11 <= -1.0e-20F) || (var_1_11 <= 9223372.036854765600e+12F && var_1_11 >= 1.0e-20F ));
 var_1_13 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_13 >= 0);
 assume_abort_if_not(var_1_13 <= 0);
 var_1_15 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_15 >= 0);
 assume_abort_if_not(var_1_15 <= 0);
 var_1_16 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_16 >= 0);
 assume_abort_if_not(var_1_16 <= 0);
 var_1_18 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_18 >= 0);
 assume_abort_if_not(var_1_18 <= 0);
}
void updateLastVariables() {
}
int property() {
 return (((((var_1_8 > var_1_8) ? (var_1_1 == ((signed long int) (((((var_1_8) < (var_1_8)) ? (var_1_8) : (var_1_8))) - 10))) : (var_1_1 == ((signed long int) (((((var_1_8 - var_1_8)) > ((var_1_8 - var_1_8))) ? ((var_1_8 - var_1_8)) : ((var_1_8 - var_1_8))))))) && (var_1_8 == ((unsigned char) (var_1_9 + 100)))) && (var_1_10 == ((float) ((((var_1_11) < (64.15f)) ? (var_1_11) : (64.15f)))))) && (((- var_1_10) > var_1_11) ? (var_1_12 == ((unsigned char) (var_1_13 || (var_1_17 && (var_1_15 || var_1_16))))) : (var_1_12 == ((unsigned char) ((var_1_1 <= var_1_9) && var_1_16))))) && ((var_1_11 <= var_1_10) ? ((var_1_1 != var_1_8) ? (var_1_17 == ((unsigned char) var_1_18)) : 1) : ((var_1_8 <= 1000000) ? (var_1_17 == ((unsigned char) 0)) : (var_1_17 == ((unsigned char) 0))))
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
