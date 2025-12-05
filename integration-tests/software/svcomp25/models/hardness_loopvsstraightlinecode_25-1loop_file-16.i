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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch1625_1loop.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
unsigned char var_1_1 = 1;
signed short int var_1_3 = 4;
signed short int var_1_4 = 256;
unsigned char var_1_5 = 0;
signed char var_1_6 = -10;
signed char var_1_7 = -4;
signed short int var_1_8 = 1;
signed short int var_1_9 = 8;
signed char var_1_10 = -32;
signed char var_1_11 = 2;
signed char var_1_12 = 8;
signed char var_1_13 = 5;
signed char var_1_14 = 32;
signed char last_1_var_1_10 = -32;
void initially(void) {
}
void step(void) {
 signed long int stepLocal_0 = var_1_4 + var_1_3;
 if (last_1_var_1_10 <= stepLocal_0) {
  var_1_6 = var_1_7;
 }
 if ((var_1_9 / var_1_4) == var_1_6) {
  var_1_10 = var_1_7;
 } else {
  if (var_1_7 >= var_1_6) {
   var_1_10 = (var_1_11 + (((((var_1_12 + var_1_13)) > (var_1_14)) ? ((var_1_12 + var_1_13)) : (var_1_14))));
  } else {
   var_1_10 = var_1_12;
  }
 }
 if ((var_1_10 % ((((var_1_3) > (var_1_4)) ? (var_1_3) : (var_1_4)))) <= -1000000) {
  var_1_1 = (((var_1_4 * var_1_3) >= var_1_10) || var_1_5);
 }
 var_1_8 = (4 - var_1_9);
}
void updateVariables() {
 var_1_3 = __VERIFIER_nondet_short();
 assume_abort_if_not(var_1_3 >= -32768);
 assume_abort_if_not(var_1_3 <= 32767);
 assume_abort_if_not(var_1_3 != 0);
 var_1_4 = __VERIFIER_nondet_short();
 assume_abort_if_not(var_1_4 >= -32768);
 assume_abort_if_not(var_1_4 <= 32767);
 assume_abort_if_not(var_1_4 != 0);
 var_1_5 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_5 >= 1);
 assume_abort_if_not(var_1_5 <= 1);
 var_1_7 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_7 >= -127);
 assume_abort_if_not(var_1_7 <= 126);
 var_1_9 = __VERIFIER_nondet_short();
 assume_abort_if_not(var_1_9 >= 0);
 assume_abort_if_not(var_1_9 <= 32766);
 var_1_11 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_11 >= -63);
 assume_abort_if_not(var_1_11 <= 63);
 var_1_12 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_12 >= -31);
 assume_abort_if_not(var_1_12 <= 32);
 var_1_13 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_13 >= -31);
 assume_abort_if_not(var_1_13 <= 31);
 var_1_14 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_14 >= -63);
 assume_abort_if_not(var_1_14 <= 63);
}
void updateLastVariables() {
 last_1_var_1_10 = var_1_10;
}
int property() {
 return (((((var_1_10 % ((((var_1_3) > (var_1_4)) ? (var_1_3) : (var_1_4)))) <= -1000000) ? (var_1_1 == ((unsigned char) (((var_1_4 * var_1_3) >= var_1_10) || var_1_5))) : 1) && ((last_1_var_1_10 <= (var_1_4 + var_1_3)) ? (var_1_6 == ((signed char) var_1_7)) : 1)) && (var_1_8 == ((signed short int) (4 - var_1_9)))) && (((var_1_9 / var_1_4) == var_1_6) ? (var_1_10 == ((signed char) var_1_7)) : ((var_1_7 >= var_1_6) ? (var_1_10 == ((signed char) (var_1_11 + (((((var_1_12 + var_1_13)) > (var_1_14)) ? ((var_1_12 + var_1_13)) : (var_1_14)))))) : (var_1_10 == ((signed char) var_1_12))))
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
