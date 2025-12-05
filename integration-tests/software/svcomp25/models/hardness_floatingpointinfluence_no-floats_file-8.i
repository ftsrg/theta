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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch8no_floats.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
unsigned char var_1_1 = 0;
unsigned char var_1_4 = 0;
unsigned char var_1_5 = 0;
unsigned char var_1_6 = 0;
unsigned char var_1_7 = 0;
signed long int var_1_8 = 64;
signed long int var_1_12 = 2;
signed long int var_1_13 = 127;
signed long int var_1_14 = 0;
signed long int var_1_15 = 31;
signed long int var_1_16 = 256;
signed long int var_1_17 = 256;
signed long int var_1_18 = 0;
unsigned char var_1_19 = 32;
unsigned char var_1_20 = 100;
void initially(void) {
}
void step(void) {
 var_1_17 = var_1_14;
 var_1_19 = var_1_20;
 var_1_18 = var_1_19;
 unsigned char stepLocal_1 = var_1_19;
 signed long int stepLocal_0 = (var_1_18 * var_1_18) * (var_1_19 - var_1_19);
 if (stepLocal_0 >= 1u) {
  if (var_1_18 <= stepLocal_1) {
   var_1_8 = var_1_19;
  } else {
   var_1_8 = var_1_19;
  }
 } else {
  var_1_8 = var_1_19;
 }
 signed long int stepLocal_2 = var_1_8;
 if (var_1_19 > stepLocal_2) {
  var_1_12 = (var_1_13 + ((var_1_14 - var_1_15) - var_1_16));
 } else {
  var_1_12 = (var_1_16 - (var_1_14 + var_1_15));
 }
 if (var_1_18 >= (8u * var_1_8)) {
  var_1_1 = (! (var_1_4 || (var_1_5 || var_1_6)));
 } else {
  var_1_1 = var_1_7;
 }
}
void updateVariables() {
 var_1_4 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_4 >= 0);
 assume_abort_if_not(var_1_4 <= 0);
 var_1_5 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_5 >= 0);
 assume_abort_if_not(var_1_5 <= 0);
 var_1_6 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_6 >= 0);
 assume_abort_if_not(var_1_6 <= 0);
 var_1_7 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_7 >= 1);
 assume_abort_if_not(var_1_7 <= 1);
 var_1_13 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_13 >= -2147483648);
 assume_abort_if_not(var_1_13 <= 2147483647);
 var_1_14 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_14 >= 2147483647);
 assume_abort_if_not(var_1_14 <= 2147483647);
 var_1_15 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_15 >= 0);
 assume_abort_if_not(var_1_15 <= 2147483647);
 var_1_16 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_16 >= 0);
 assume_abort_if_not(var_1_16 <= 2147483647);
 var_1_20 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_20 >= 0);
 assume_abort_if_not(var_1_20 <= 254);
}
void updateLastVariables() {
}
int property() {
 return ((((((var_1_18 >= (8u * var_1_8)) ? (var_1_1 == ((unsigned char) (! (var_1_4 || (var_1_5 || var_1_6))))) : (var_1_1 == ((unsigned char) var_1_7))) && ((((var_1_18 * var_1_18) * (var_1_19 - var_1_19)) >= 1u) ? ((var_1_18 <= var_1_19) ? (var_1_8 == ((signed long int) var_1_19)) : (var_1_8 == ((signed long int) var_1_19))) : (var_1_8 == ((signed long int) var_1_19)))) && ((var_1_19 > var_1_8) ? (var_1_12 == ((signed long int) (var_1_13 + ((var_1_14 - var_1_15) - var_1_16)))) : (var_1_12 == ((signed long int) (var_1_16 - (var_1_14 + var_1_15)))))) && (var_1_17 == ((signed long int) var_1_14))) && (var_1_18 == ((signed long int) var_1_19))) && (var_1_19 == ((unsigned char) var_1_20))
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
