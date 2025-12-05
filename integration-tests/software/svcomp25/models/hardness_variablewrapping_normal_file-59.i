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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch59normal.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
signed long int var_1_1 = -128;
signed long int var_1_4 = 0;
signed char var_1_7 = -1;
signed long int var_1_8 = 32;
signed char var_1_9 = 32;
signed char var_1_10 = -4;
signed char var_1_11 = -4;
signed short int var_1_12 = -32;
signed short int var_1_13 = 128;
signed short int var_1_14 = 1000;
unsigned char var_1_15 = 0;
unsigned char var_1_16 = 0;
signed long int last_1_var_1_1 = -128;
signed char last_1_var_1_7 = -1;
signed short int last_1_var_1_12 = -32;
void initially(void) {
}
void step(void) {
 if (last_1_var_1_1 > ((((last_1_var_1_7) < 0 ) ? -(last_1_var_1_7) : (last_1_var_1_7)))) {
  var_1_12 = (var_1_13 - var_1_14);
 } else {
  if (var_1_15 || var_1_16) {
   if (2 < last_1_var_1_7) {
    var_1_12 = last_1_var_1_7;
   }
  }
 }
 if (last_1_var_1_12 > (last_1_var_1_7 * (var_1_4 - var_1_8))) {
  if (var_1_8 > last_1_var_1_7) {
   var_1_7 = ((var_1_9 + var_1_10) + var_1_11);
  } else {
   var_1_7 = var_1_10;
  }
 } else {
  var_1_7 = var_1_11;
 }
 if (((((var_1_12) > (1)) ? (var_1_12) : (1))) <= (256 + last_1_var_1_1)) {
  var_1_1 = (((var_1_4 - 128) + var_1_12) + var_1_7);
 } else {
  var_1_1 = (var_1_4 + var_1_12);
 }
}
void updateVariables() {
 var_1_4 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_4 >= 0);
 assume_abort_if_not(var_1_4 <= 536870912);
 var_1_8 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_8 >= 0);
 assume_abort_if_not(var_1_8 <= 2147483647);
 var_1_9 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_9 >= -31);
 assume_abort_if_not(var_1_9 <= 32);
 var_1_10 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_10 >= -31);
 assume_abort_if_not(var_1_10 <= 31);
 var_1_11 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_11 >= -63);
 assume_abort_if_not(var_1_11 <= 63);
 var_1_13 = __VERIFIER_nondet_short();
 assume_abort_if_not(var_1_13 >= -1);
 assume_abort_if_not(var_1_13 <= 32766);
 var_1_14 = __VERIFIER_nondet_short();
 assume_abort_if_not(var_1_14 >= 0);
 assume_abort_if_not(var_1_14 <= 32766);
 var_1_15 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_15 >= 0);
 assume_abort_if_not(var_1_15 <= 1);
 var_1_16 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_16 >= 0);
 assume_abort_if_not(var_1_16 <= 1);
}
void updateLastVariables() {
 last_1_var_1_1 = var_1_1;
 last_1_var_1_7 = var_1_7;
 last_1_var_1_12 = var_1_12;
}
int property() {
 return (((((((var_1_12) > (1)) ? (var_1_12) : (1))) <= (256 + last_1_var_1_1)) ? (var_1_1 == ((signed long int) (((var_1_4 - 128) + var_1_12) + var_1_7))) : (var_1_1 == ((signed long int) (var_1_4 + var_1_12)))) && ((last_1_var_1_12 > (last_1_var_1_7 * (var_1_4 - var_1_8))) ? ((var_1_8 > last_1_var_1_7) ? (var_1_7 == ((signed char) ((var_1_9 + var_1_10) + var_1_11))) : (var_1_7 == ((signed char) var_1_10))) : (var_1_7 == ((signed char) var_1_11)))) && ((last_1_var_1_1 > ((((last_1_var_1_7) < 0 ) ? -(last_1_var_1_7) : (last_1_var_1_7)))) ? (var_1_12 == ((signed short int) (var_1_13 - var_1_14))) : ((var_1_15 || var_1_16) ? ((2 < last_1_var_1_7) ? (var_1_12 == ((signed short int) last_1_var_1_7)) : 1) : 1))
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
