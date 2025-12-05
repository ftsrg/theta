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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch525_1loop.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
signed short int var_1_1 = 10000;
signed long int var_1_4 = 10000000;
signed short int var_1_7 = 4;
unsigned char var_1_8 = 10;
unsigned char var_1_9 = 0;
signed short int var_1_10 = 2;
unsigned char var_1_11 = 0;
unsigned char var_1_12 = 32;
unsigned char var_1_13 = 4;
signed long int var_1_14 = -25;
unsigned long int var_1_15 = 256;
unsigned char last_1_var_1_8 = 10;
void initially(void) {
}
void step(void) {
 signed short int stepLocal_1 = var_1_7;
 if (var_1_9) {
  if (stepLocal_1 > (var_1_4 + (last_1_var_1_8 - var_1_10))) {
   if (var_1_11) {
    var_1_8 = var_1_12;
   } else {
    var_1_8 = var_1_13;
   }
  } else {
   var_1_8 = var_1_13;
  }
 }
 signed long int stepLocal_3 = -2;
 if (var_1_8 >= stepLocal_3) {
  var_1_15 = ((((var_1_12) > (var_1_8)) ? (var_1_12) : (var_1_8)));
 }
 signed long int stepLocal_0 = var_1_8 - var_1_8;
 if ((var_1_8 - var_1_8) >= stepLocal_0) {
  var_1_1 = ((((var_1_8 - var_1_8) < 0 ) ? -(var_1_8 - var_1_8) : (var_1_8 - var_1_8)));
 }
 signed long int stepLocal_2 = (((var_1_8) < (var_1_8)) ? (var_1_8) : (var_1_8));
 if (stepLocal_2 > ((((var_1_15) < (var_1_8)) ? (var_1_15) : (var_1_8)))) {
  var_1_14 = var_1_8;
 }
}
void updateVariables() {
 var_1_4 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_4 >= -1);
 assume_abort_if_not(var_1_4 <= 2147483647);
 var_1_7 = __VERIFIER_nondet_short();
 assume_abort_if_not(var_1_7 >= 0);
 assume_abort_if_not(var_1_7 <= 32766);
 var_1_9 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_9 >= 0);
 assume_abort_if_not(var_1_9 <= 1);
 var_1_10 = __VERIFIER_nondet_short();
 assume_abort_if_not(var_1_10 >= 0);
 assume_abort_if_not(var_1_10 <= 32767);
 var_1_11 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_11 >= 0);
 assume_abort_if_not(var_1_11 <= 1);
 var_1_12 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_12 >= 0);
 assume_abort_if_not(var_1_12 <= 254);
 var_1_13 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_13 >= 0);
 assume_abort_if_not(var_1_13 <= 254);
}
void updateLastVariables() {
 last_1_var_1_8 = var_1_8;
}
int property() {
 return (((((var_1_8 - var_1_8) >= (var_1_8 - var_1_8)) ? (var_1_1 == ((signed short int) ((((var_1_8 - var_1_8) < 0 ) ? -(var_1_8 - var_1_8) : (var_1_8 - var_1_8))))) : 1) && (var_1_9 ? ((var_1_7 > (var_1_4 + (last_1_var_1_8 - var_1_10))) ? (var_1_11 ? (var_1_8 == ((unsigned char) var_1_12)) : (var_1_8 == ((unsigned char) var_1_13))) : (var_1_8 == ((unsigned char) var_1_13))) : 1)) && ((((((var_1_8) < (var_1_8)) ? (var_1_8) : (var_1_8))) > ((((var_1_15) < (var_1_8)) ? (var_1_15) : (var_1_8)))) ? (var_1_14 == ((signed long int) var_1_8)) : 1)) && ((var_1_8 >= -2) ? (var_1_15 == ((unsigned long int) ((((var_1_12) > (var_1_8)) ? (var_1_12) : (var_1_8))))) : 1)
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
