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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch88normal.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
signed char var_1_1 = -8;
unsigned char var_1_5 = 0;
unsigned char var_1_6 = 1;
signed char var_1_7 = -1;
signed char var_1_8 = -50;
signed char var_1_9 = 100;
unsigned long int var_1_10 = 25;
unsigned long int var_1_11 = 2568920345;
unsigned long int var_1_12 = 1191097264;
unsigned long int var_1_13 = 1801344522;
signed long int var_1_14 = 64;
signed short int var_1_15 = -16;
float var_1_16 = 1000000.5;
float var_1_17 = 4.5;
unsigned char var_1_18 = 0;
unsigned char var_1_19 = 128;
unsigned long int last_1_var_1_10 = 25;
signed short int last_1_var_1_15 = -16;
unsigned char last_1_var_1_18 = 0;
void initially(void) {
}
void step(void) {
 if (((last_1_var_1_15 | last_1_var_1_10) > last_1_var_1_18) && var_1_5) {
  if (var_1_5 && var_1_6) {
   var_1_1 = var_1_7;
  } else {
   var_1_1 = var_1_7;
  }
 } else {
  var_1_1 = var_1_7;
 }
 if (var_1_5) {
  var_1_8 = ((((var_1_7) > (var_1_9)) ? (var_1_7) : (var_1_9)));
 }
 if (var_1_12 <= var_1_8) {
  var_1_14 = ((((var_1_8) < 0 ) ? -(var_1_8) : (var_1_8)));
 }
 var_1_15 = 2;
 var_1_16 = var_1_17;
 var_1_18 = var_1_19;
 unsigned char stepLocal_0 = var_1_8 < var_1_1;
 if (stepLocal_0 && (((((var_1_9) > (var_1_8)) ? (var_1_9) : (var_1_8))) == var_1_7)) {
  var_1_10 = (var_1_11 - (((((var_1_12) > (var_1_13)) ? (var_1_12) : (var_1_13))) - 1u));
 } else {
  var_1_10 = (var_1_11 - var_1_13);
 }
}
void updateVariables() {
 var_1_5 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_5 >= 0);
 assume_abort_if_not(var_1_5 <= 1);
 var_1_6 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_6 >= 0);
 assume_abort_if_not(var_1_6 <= 1);
 var_1_7 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_7 >= -127);
 assume_abort_if_not(var_1_7 <= 126);
 var_1_9 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_9 >= -127);
 assume_abort_if_not(var_1_9 <= 126);
 var_1_11 = __VERIFIER_nondet_ulong();
 assume_abort_if_not(var_1_11 >= 2147483647);
 assume_abort_if_not(var_1_11 <= 4294967294);
 var_1_12 = __VERIFIER_nondet_ulong();
 assume_abort_if_not(var_1_12 >= 1073741823);
 assume_abort_if_not(var_1_12 <= 2147483647);
 var_1_13 = __VERIFIER_nondet_ulong();
 assume_abort_if_not(var_1_13 >= 1073741823);
 assume_abort_if_not(var_1_13 <= 2147483647);
 var_1_17 = __VERIFIER_nondet_float();
 assume_abort_if_not((var_1_17 >= -922337.2036854765600e+13F && var_1_17 <= -1.0e-20F) || (var_1_17 <= 9223372.036854765600e+12F && var_1_17 >= 1.0e-20F ));
 var_1_19 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_19 >= 0);
 assume_abort_if_not(var_1_19 <= 254);
}
void updateLastVariables() {
 last_1_var_1_10 = var_1_10;
 last_1_var_1_15 = var_1_15;
 last_1_var_1_18 = var_1_18;
}
int property() {
 return (((((((((last_1_var_1_15 | last_1_var_1_10) > last_1_var_1_18) && var_1_5) ? ((var_1_5 && var_1_6) ? (var_1_1 == ((signed char) var_1_7)) : (var_1_1 == ((signed char) var_1_7))) : (var_1_1 == ((signed char) var_1_7))) && (var_1_5 ? (var_1_8 == ((signed char) ((((var_1_7) > (var_1_9)) ? (var_1_7) : (var_1_9))))) : 1)) && (((var_1_8 < var_1_1) && (((((var_1_9) > (var_1_8)) ? (var_1_9) : (var_1_8))) == var_1_7)) ? (var_1_10 == ((unsigned long int) (var_1_11 - (((((var_1_12) > (var_1_13)) ? (var_1_12) : (var_1_13))) - 1u)))) : (var_1_10 == ((unsigned long int) (var_1_11 - var_1_13))))) && ((var_1_12 <= var_1_8) ? (var_1_14 == ((signed long int) ((((var_1_8) < 0 ) ? -(var_1_8) : (var_1_8))))) : 1)) && (var_1_15 == ((signed short int) 2))) && (var_1_16 == ((float) var_1_17))) && (var_1_18 == ((unsigned char) var_1_19))
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
