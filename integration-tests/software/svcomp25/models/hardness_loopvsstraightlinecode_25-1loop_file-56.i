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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch5625_1loop.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
unsigned char var_1_1 = 1;
signed char var_1_3 = 0;
unsigned char var_1_5 = 128;
unsigned char var_1_6 = 16;
unsigned char var_1_7 = 2;
unsigned long int var_1_8 = 1000000;
unsigned long int var_1_10 = 2131342500;
unsigned short int var_1_11 = 0;
signed short int var_1_12 = -4;
unsigned char last_1_var_1_1 = 1;
unsigned short int last_1_var_1_11 = 0;
void initially(void) {
}
void step(void) {
 if ((last_1_var_1_11 >> var_1_3) >= last_1_var_1_1) {
  var_1_1 = ((((var_1_3) < ((var_1_5 - ((((var_1_6) > (var_1_7)) ? (var_1_6) : (var_1_7)))))) ? (var_1_3) : ((var_1_5 - ((((var_1_6) > (var_1_7)) ? (var_1_6) : (var_1_7)))))));
 } else {
  var_1_1 = var_1_6;
 }
 var_1_12 = var_1_1;
 signed long int stepLocal_3 = 25 + (var_1_12 * var_1_6);
 unsigned long int stepLocal_2 = var_1_10;
 if ((var_1_1 % var_1_5) > stepLocal_2) {
  if (stepLocal_3 >= var_1_5) {
   var_1_11 = var_1_7;
  }
 }
 signed long int stepLocal_1 = 8 + var_1_11;
 signed char stepLocal_0 = var_1_3;
 if (var_1_11 >= stepLocal_1) {
  if (var_1_5 < stepLocal_0) {
   var_1_8 = ((var_1_10 - var_1_5) + var_1_11);
  }
 }
}
void updateVariables() {
 var_1_3 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_3 >= 0);
 assume_abort_if_not(var_1_3 <= 16);
 var_1_5 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_5 >= 127);
 assume_abort_if_not(var_1_5 <= 254);
 var_1_6 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_6 >= 0);
 assume_abort_if_not(var_1_6 <= 127);
 var_1_7 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_7 >= 0);
 assume_abort_if_not(var_1_7 <= 127);
 var_1_10 = __VERIFIER_nondet_ulong();
 assume_abort_if_not(var_1_10 >= 1073741823);
 assume_abort_if_not(var_1_10 <= 2147483647);
}
void updateLastVariables() {
 last_1_var_1_1 = var_1_1;
 last_1_var_1_11 = var_1_11;
}
int property() {
 return (((((last_1_var_1_11 >> var_1_3) >= last_1_var_1_1) ? (var_1_1 == ((unsigned char) ((((var_1_3) < ((var_1_5 - ((((var_1_6) > (var_1_7)) ? (var_1_6) : (var_1_7)))))) ? (var_1_3) : ((var_1_5 - ((((var_1_6) > (var_1_7)) ? (var_1_6) : (var_1_7))))))))) : (var_1_1 == ((unsigned char) var_1_6))) && ((var_1_11 >= (8 + var_1_11)) ? ((var_1_5 < var_1_3) ? (var_1_8 == ((unsigned long int) ((var_1_10 - var_1_5) + var_1_11))) : 1) : 1)) && (((var_1_1 % var_1_5) > var_1_10) ? (((25 + (var_1_12 * var_1_6)) >= var_1_5) ? (var_1_11 == ((unsigned short int) var_1_7)) : 1) : 1)) && (var_1_12 == ((signed short int) var_1_1))
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
