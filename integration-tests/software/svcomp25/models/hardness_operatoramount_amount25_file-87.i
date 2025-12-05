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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch87Amount25.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
unsigned long int var_1_1 = 1;
unsigned char var_1_2 = 0;
unsigned long int var_1_3 = 3164414017;
unsigned long int var_1_4 = 128;
signed char var_1_5 = -128;
signed char var_1_6 = 10;
signed char var_1_7 = 50;
float var_1_8 = 5.1;
float var_1_9 = 63.75;
signed char var_1_10 = 100;
signed long int var_1_12 = 5;
signed char last_1_var_1_10 = 100;
void initially(void) {
}
void step(void) {
 if (var_1_2) {
  var_1_1 = ((((var_1_3 - var_1_4) < 0 ) ? -(var_1_3 - var_1_4) : (var_1_3 - var_1_4)));
 }
 signed long int stepLocal_1 = -8;
 unsigned long int stepLocal_0 = var_1_1;
 if (stepLocal_1 < var_1_4) {
  if (var_1_4 != stepLocal_0) {
   var_1_5 = (((((var_1_6) < 0 ) ? -(var_1_6) : (var_1_6))) - var_1_7);
  } else {
   var_1_5 = var_1_6;
  }
 } else {
  var_1_5 = -2;
 }
 unsigned long int stepLocal_3 = var_1_1;
 unsigned long int stepLocal_2 = var_1_4 >> var_1_3;
 if (var_1_6 >= stepLocal_2) {
  if (var_1_6 != stepLocal_3) {
   var_1_8 = var_1_9;
  }
 }
 if ((var_1_1 + (var_1_6 / var_1_12)) < var_1_1) {
  if (var_1_7 >= last_1_var_1_10) {
   var_1_10 = -32;
  } else {
   var_1_10 = var_1_7;
  }
 }
}
void updateVariables() {
 var_1_2 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_2 >= 0);
 assume_abort_if_not(var_1_2 <= 1);
 var_1_3 = __VERIFIER_nondet_ulong();
 assume_abort_if_not(var_1_3 >= 2147483647);
 assume_abort_if_not(var_1_3 <= 4294967294);
 var_1_4 = __VERIFIER_nondet_ulong();
 assume_abort_if_not(var_1_4 >= 0);
 assume_abort_if_not(var_1_4 <= 2147483647);
 var_1_6 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_6 >= -126);
 assume_abort_if_not(var_1_6 <= 126);
 var_1_7 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_7 >= 0);
 assume_abort_if_not(var_1_7 <= 126);
 var_1_9 = __VERIFIER_nondet_float();
 assume_abort_if_not((var_1_9 >= -922337.2036854765600e+13F && var_1_9 <= -1.0e-20F) || (var_1_9 <= 9223372.036854765600e+12F && var_1_9 >= 1.0e-20F ));
 var_1_12 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_12 >= -2147483648);
 assume_abort_if_not(var_1_12 <= 2147483647);
 assume_abort_if_not(var_1_12 != 0);
}
void updateLastVariables() {
 last_1_var_1_10 = var_1_10;
}
int property() {
 return (((var_1_2 ? (var_1_1 == ((unsigned long int) ((((var_1_3 - var_1_4) < 0 ) ? -(var_1_3 - var_1_4) : (var_1_3 - var_1_4))))) : 1) && ((-8 < var_1_4) ? ((var_1_4 != var_1_1) ? (var_1_5 == ((signed char) (((((var_1_6) < 0 ) ? -(var_1_6) : (var_1_6))) - var_1_7))) : (var_1_5 == ((signed char) var_1_6))) : (var_1_5 == ((signed char) -2)))) && ((var_1_6 >= (var_1_4 >> var_1_3)) ? ((var_1_6 != var_1_1) ? (var_1_8 == ((float) var_1_9)) : 1) : 1)) && (((var_1_1 + (var_1_6 / var_1_12)) < var_1_1) ? ((var_1_7 >= last_1_var_1_10) ? (var_1_10 == ((signed char) -32)) : (var_1_10 == ((signed char) var_1_7))) : 1)
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
