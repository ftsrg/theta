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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch425_1loop.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
unsigned short int var_1_1 = 5;
signed short int var_1_3 = -25;
unsigned short int var_1_5 = 256;
unsigned short int var_1_6 = 25;
unsigned short int var_1_7 = 4;
unsigned char var_1_8 = 1;
unsigned short int var_1_9 = 4;
unsigned char var_1_10 = 1;
unsigned short int var_1_11 = 41562;
unsigned short int var_1_12 = 25;
unsigned short int last_1_var_1_9 = 4;
void initially(void) {
}
void step(void) {
 signed long int stepLocal_1 = last_1_var_1_9 / var_1_3;
 signed long int stepLocal_0 = last_1_var_1_9;
 if (stepLocal_1 >= last_1_var_1_9) {
  if ((- var_1_3) > stepLocal_0) {
   var_1_1 = ((((var_1_5) < (var_1_6)) ? (var_1_5) : (var_1_6)));
  }
 }
 unsigned char stepLocal_4 = var_1_10;
 signed long int stepLocal_3 = ((((64513) < (var_1_11)) ? (64513) : (var_1_11))) - var_1_12;
 if (var_1_8 || stepLocal_4) {
  var_1_9 = ((((var_1_5) < (var_1_6)) ? (var_1_5) : (var_1_6)));
 } else {
  if (stepLocal_3 >= (5 * var_1_1)) {
   var_1_9 = var_1_6;
  } else {
   var_1_9 = var_1_12;
  }
 }
 signed long int stepLocal_2 = var_1_9 * (var_1_3 + var_1_1);
 if (var_1_8) {
  if (stepLocal_2 > var_1_9) {
   var_1_7 = 256;
  }
 }
}
void updateVariables() {
 var_1_3 = __VERIFIER_nondet_short();
 assume_abort_if_not(var_1_3 >= -32768);
 assume_abort_if_not(var_1_3 <= 32767);
 assume_abort_if_not(var_1_3 != 0);
 var_1_5 = __VERIFIER_nondet_ushort();
 assume_abort_if_not(var_1_5 >= 0);
 assume_abort_if_not(var_1_5 <= 65534);
 var_1_6 = __VERIFIER_nondet_ushort();
 assume_abort_if_not(var_1_6 >= 0);
 assume_abort_if_not(var_1_6 <= 65534);
 var_1_8 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_8 >= 0);
 assume_abort_if_not(var_1_8 <= 1);
 var_1_10 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_10 >= 0);
 assume_abort_if_not(var_1_10 <= 1);
 var_1_11 = __VERIFIER_nondet_ushort();
 assume_abort_if_not(var_1_11 >= 32767);
 assume_abort_if_not(var_1_11 <= 65535);
 var_1_12 = __VERIFIER_nondet_ushort();
 assume_abort_if_not(var_1_12 >= 0);
 assume_abort_if_not(var_1_12 <= 32767);
}
void updateLastVariables() {
 last_1_var_1_9 = var_1_9;
}
int property() {
 return ((((last_1_var_1_9 / var_1_3) >= last_1_var_1_9) ? (((- var_1_3) > last_1_var_1_9) ? (var_1_1 == ((unsigned short int) ((((var_1_5) < (var_1_6)) ? (var_1_5) : (var_1_6))))) : 1) : 1) && (var_1_8 ? (((var_1_9 * (var_1_3 + var_1_1)) > var_1_9) ? (var_1_7 == ((unsigned short int) 256)) : 1) : 1)) && ((var_1_8 || var_1_10) ? (var_1_9 == ((unsigned short int) ((((var_1_5) < (var_1_6)) ? (var_1_5) : (var_1_6))))) : (((((((64513) < (var_1_11)) ? (64513) : (var_1_11))) - var_1_12) >= (5 * var_1_1)) ? (var_1_9 == ((unsigned short int) var_1_6)) : (var_1_9 == ((unsigned short int) var_1_12))))
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
