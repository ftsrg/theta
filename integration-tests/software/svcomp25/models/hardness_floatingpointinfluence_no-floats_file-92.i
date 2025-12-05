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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch92no_floats.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
signed char var_1_1 = 32;
signed char var_1_2 = 2;
signed char var_1_3 = 8;
signed char var_1_4 = 0;
signed char var_1_5 = 32;
signed char var_1_6 = 10;
signed long int var_1_7 = 1000000;
signed long int var_1_8 = 16;
signed long int var_1_9 = 15;
signed short int var_1_10 = 500;
unsigned short int var_1_11 = 8;
unsigned char var_1_13 = 0;
unsigned short int var_1_14 = 100;
unsigned char var_1_15 = 0;
unsigned char var_1_16 = 0;
signed long int var_1_17 = 2;
void initially(void) {
}
void step(void) {
 var_1_1 = ((var_1_2 + var_1_3) - ((((var_1_4) > ((var_1_5 + var_1_6))) ? (var_1_4) : ((var_1_5 + var_1_6)))));
 signed long int stepLocal_0 = (~ var_1_5) * (var_1_6 & var_1_3);
 if (stepLocal_0 >= var_1_4) {
  var_1_7 = var_1_8;
 } else {
  var_1_7 = var_1_9;
 }
 var_1_10 = ((((var_1_2) < 0 ) ? -(var_1_2) : (var_1_2)));
 signed long int stepLocal_1 = var_1_6 / var_1_14;
 if (stepLocal_1 < -100) {
  var_1_13 = (! (! (! var_1_15)));
 } else {
  var_1_13 = (var_1_15 && var_1_16);
 }
 var_1_17 = var_1_8;
 if (! var_1_13) {
  var_1_11 = (var_1_5 + (((((var_1_6) > (1)) ? (var_1_6) : (1))) + 64));
 }
}
void updateVariables() {
 var_1_2 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_2 >= 0);
 assume_abort_if_not(var_1_2 <= 63);
 var_1_3 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_3 >= 0);
 assume_abort_if_not(var_1_3 <= 63);
 var_1_4 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_4 >= 0);
 assume_abort_if_not(var_1_4 <= 126);
 var_1_5 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_5 >= 0);
 assume_abort_if_not(var_1_5 <= 63);
 var_1_6 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_6 >= 0);
 assume_abort_if_not(var_1_6 <= 63);
 var_1_8 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_8 >= -2147483648);
 assume_abort_if_not(var_1_8 <= 2147483647);
 var_1_9 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_9 >= -2147483648);
 assume_abort_if_not(var_1_9 <= 2147483647);
 var_1_14 = __VERIFIER_nondet_ushort();
 assume_abort_if_not(var_1_14 >= 0);
 assume_abort_if_not(var_1_14 <= 65535);
 assume_abort_if_not(var_1_14 != 0);
 var_1_15 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_15 >= 0);
 assume_abort_if_not(var_1_15 <= 0);
 var_1_16 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_16 >= 0);
 assume_abort_if_not(var_1_16 <= 0);
}
void updateLastVariables() {
}
int property() {
 return (((((var_1_1 == ((signed char) ((var_1_2 + var_1_3) - ((((var_1_4) > ((var_1_5 + var_1_6))) ? (var_1_4) : ((var_1_5 + var_1_6))))))) && ((((~ var_1_5) * (var_1_6 & var_1_3)) >= var_1_4) ? (var_1_7 == ((signed long int) var_1_8)) : (var_1_7 == ((signed long int) var_1_9)))) && (var_1_10 == ((signed short int) ((((var_1_2) < 0 ) ? -(var_1_2) : (var_1_2)))))) && ((! var_1_13) ? (var_1_11 == ((unsigned short int) (var_1_5 + (((((var_1_6) > (1)) ? (var_1_6) : (1))) + 64)))) : 1)) && (((var_1_6 / var_1_14) < -100) ? (var_1_13 == ((unsigned char) (! (! (! var_1_15))))) : (var_1_13 == ((unsigned char) (var_1_15 && var_1_16))))) && (var_1_17 == ((signed long int) var_1_8))
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
