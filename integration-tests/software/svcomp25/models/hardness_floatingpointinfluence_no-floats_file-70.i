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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch70no_floats.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
unsigned short int var_1_1 = 0;
unsigned char var_1_2 = 0;
unsigned short int var_1_4 = 19138;
signed char var_1_6 = 25;
signed long int var_1_7 = -50;
signed long int var_1_8 = 8;
signed long int var_1_9 = 255;
signed long int var_1_10 = 10000000;
signed long int var_1_11 = 0;
signed long int var_1_12 = 255;
unsigned char var_1_13 = 50;
unsigned char var_1_14 = 2;
signed char var_1_15 = 1;
signed char var_1_16 = 5;
void initially(void) {
}
void step(void) {
 var_1_13 = var_1_14;
 var_1_15 = var_1_16;
 if (var_1_2) {
  var_1_1 = ((17222 - var_1_13) + (((((29916) < (var_1_4)) ? (29916) : (var_1_4))) - var_1_13));
 }
 if (var_1_2 && (var_1_4 >= (var_1_13 + var_1_1))) {
  var_1_6 = 8;
 }
 unsigned short int stepLocal_0 = var_1_4;
 if (stepLocal_0 <= ((((var_1_13) > ((var_1_13 << var_1_13))) ? (var_1_13) : ((var_1_13 << var_1_13))))) {
  var_1_7 = (((((var_1_13 - var_1_13)) < (var_1_4)) ? ((var_1_13 - var_1_13)) : (var_1_4)));
 } else {
  var_1_7 = (var_1_13 + (var_1_1 + var_1_4));
 }
 unsigned char stepLocal_1 = var_1_13;
 if (var_1_13 < stepLocal_1) {
  var_1_8 = (var_1_9 - var_1_10);
 } else {
  var_1_8 = ((var_1_11 - var_1_12) - var_1_9);
 }
}
void updateVariables() {
 var_1_2 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_2 >= 0);
 assume_abort_if_not(var_1_2 <= 1);
 var_1_4 = __VERIFIER_nondet_ushort();
 assume_abort_if_not(var_1_4 >= 16383);
 assume_abort_if_not(var_1_4 <= 32767);
 var_1_9 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_9 >= 0);
 assume_abort_if_not(var_1_9 <= 2147483647);
 var_1_10 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_10 >= 0);
 assume_abort_if_not(var_1_10 <= 2147483647);
 var_1_11 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_11 >= 2147483647);
 assume_abort_if_not(var_1_11 <= 2147483647);
 var_1_12 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_12 >= 0);
 assume_abort_if_not(var_1_12 <= 2147483647);
 var_1_14 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_14 >= 0);
 assume_abort_if_not(var_1_14 <= 254);
 var_1_16 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_16 >= -127);
 assume_abort_if_not(var_1_16 <= 126);
}
void updateLastVariables() {
}
int property() {
 return (((((var_1_2 ? (var_1_1 == ((unsigned short int) ((17222 - var_1_13) + (((((29916) < (var_1_4)) ? (29916) : (var_1_4))) - var_1_13)))) : 1) && ((var_1_2 && (var_1_4 >= (var_1_13 + var_1_1))) ? (var_1_6 == ((signed char) 8)) : 1)) && ((var_1_4 <= ((((var_1_13) > ((var_1_13 << var_1_13))) ? (var_1_13) : ((var_1_13 << var_1_13))))) ? (var_1_7 == ((signed long int) (((((var_1_13 - var_1_13)) < (var_1_4)) ? ((var_1_13 - var_1_13)) : (var_1_4))))) : (var_1_7 == ((signed long int) (var_1_13 + (var_1_1 + var_1_4)))))) && ((var_1_13 < var_1_13) ? (var_1_8 == ((signed long int) (var_1_9 - var_1_10))) : (var_1_8 == ((signed long int) ((var_1_11 - var_1_12) - var_1_9))))) && (var_1_13 == ((unsigned char) var_1_14))) && (var_1_15 == ((signed char) var_1_16))
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
