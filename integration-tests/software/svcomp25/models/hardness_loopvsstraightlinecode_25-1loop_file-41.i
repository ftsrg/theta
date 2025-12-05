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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch4125_1loop.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
signed char var_1_1 = -16;
unsigned char var_1_5 = 0;
signed char var_1_6 = -8;
signed char var_1_7 = -2;
unsigned char var_1_8 = 1;
unsigned char var_1_9 = 0;
unsigned long int var_1_10 = 128;
unsigned long int var_1_11 = 25;
unsigned long int var_1_12 = 1879943783;
unsigned long int var_1_13 = 128;
unsigned long int var_1_14 = 2555856598;
unsigned long int var_1_15 = 10;
void initially(void) {
}
void step(void) {
 if (var_1_5) {
  var_1_8 = (! (! var_1_9));
 }
 unsigned char stepLocal_1 = var_1_9;
 if ((-2 != var_1_7) || stepLocal_1) {
  var_1_10 = (var_1_11 + (var_1_12 - var_1_13));
 } else {
  var_1_10 = (var_1_14 - var_1_13);
 }
 if (var_1_10 < var_1_10) {
  if (var_1_12 == (var_1_14 - var_1_13)) {
   var_1_15 = var_1_12;
  }
 }
 unsigned long int stepLocal_0 = (var_1_10 & 0u) * var_1_10;
 if (stepLocal_0 > var_1_10) {
  if (var_1_8) {
   var_1_1 = var_1_6;
  } else {
   var_1_1 = var_1_7;
  }
 } else {
  var_1_1 = var_1_7;
 }
}
void updateVariables() {
 var_1_5 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_5 >= 0);
 assume_abort_if_not(var_1_5 <= 1);
 var_1_6 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_6 >= -127);
 assume_abort_if_not(var_1_6 <= 126);
 var_1_7 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_7 >= -127);
 assume_abort_if_not(var_1_7 <= 126);
 var_1_9 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_9 >= 0);
 assume_abort_if_not(var_1_9 <= 0);
 var_1_11 = __VERIFIER_nondet_ulong();
 assume_abort_if_not(var_1_11 >= 0);
 assume_abort_if_not(var_1_11 <= 2147483647);
 var_1_12 = __VERIFIER_nondet_ulong();
 assume_abort_if_not(var_1_12 >= 1073741823);
 assume_abort_if_not(var_1_12 <= 2147483647);
 var_1_13 = __VERIFIER_nondet_ulong();
 assume_abort_if_not(var_1_13 >= 0);
 assume_abort_if_not(var_1_13 <= 1073741823);
 var_1_14 = __VERIFIER_nondet_ulong();
 assume_abort_if_not(var_1_14 >= 2147483647);
 assume_abort_if_not(var_1_14 <= 4294967294);
}
void updateLastVariables() {
}
int property() {
 return ((((((var_1_10 & 0u) * var_1_10) > var_1_10) ? (var_1_8 ? (var_1_1 == ((signed char) var_1_6)) : (var_1_1 == ((signed char) var_1_7))) : (var_1_1 == ((signed char) var_1_7))) && (var_1_5 ? (var_1_8 == ((unsigned char) (! (! var_1_9)))) : 1)) && (((-2 != var_1_7) || var_1_9) ? (var_1_10 == ((unsigned long int) (var_1_11 + (var_1_12 - var_1_13)))) : (var_1_10 == ((unsigned long int) (var_1_14 - var_1_13))))) && ((var_1_10 < var_1_10) ? ((var_1_12 == (var_1_14 - var_1_13)) ? (var_1_15 == ((unsigned long int) var_1_12)) : 1) : 1)
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
