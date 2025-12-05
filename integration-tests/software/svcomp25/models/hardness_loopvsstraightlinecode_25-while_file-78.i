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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch7825_while.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
signed long int var_1_1 = -200;
unsigned char var_1_2 = 0;
unsigned char var_1_3 = 1;
signed long int var_1_6 = 128;
signed long int var_1_7 = 10;
signed short int var_1_8 = 0;
signed short int var_1_9 = 25;
signed short int var_1_10 = 32;
signed short int var_1_11 = 1000;
signed short int var_1_12 = 25;
signed short int var_1_13 = 128;
unsigned long int var_1_14 = 5;
float var_1_15 = 8.25;
float var_1_16 = 63.5;
float var_1_17 = -0.6;
signed long int last_1_var_1_1 = -200;
void initially(void) {
}
void step(void) {
 if (var_1_3) {
  var_1_14 = (2931747731u - var_1_10);
 }
 unsigned char stepLocal_1 = var_1_3;
 unsigned char stepLocal_0 = var_1_2;
 if (var_1_2 && stepLocal_1) {
  if (stepLocal_0 && (var_1_14 > last_1_var_1_1)) {
   var_1_1 = (var_1_6 - var_1_7);
  } else {
   var_1_1 = var_1_6;
  }
 }
 if (var_1_14 > var_1_14) {
  var_1_8 = ((var_1_9 - var_1_10) + ((((-4) < ((var_1_11 + var_1_12))) ? (-4) : ((var_1_11 + var_1_12)))));
 } else {
  var_1_8 = (((((var_1_9) < (var_1_10)) ? (var_1_9) : (var_1_10))) - var_1_13);
 }
 if (var_1_11 >= var_1_1) {
  var_1_15 = ((((var_1_16) > (var_1_17)) ? (var_1_16) : (var_1_17)));
 }
}
void updateVariables() {
 var_1_2 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_2 >= 0);
 assume_abort_if_not(var_1_2 <= 1);
 var_1_3 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_3 >= 0);
 assume_abort_if_not(var_1_3 <= 1);
 var_1_6 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_6 >= -1);
 assume_abort_if_not(var_1_6 <= 2147483646);
 var_1_7 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_7 >= 0);
 assume_abort_if_not(var_1_7 <= 2147483646);
 var_1_9 = __VERIFIER_nondet_short();
 assume_abort_if_not(var_1_9 >= 0);
 assume_abort_if_not(var_1_9 <= 16383);
 var_1_10 = __VERIFIER_nondet_short();
 assume_abort_if_not(var_1_10 >= 0);
 assume_abort_if_not(var_1_10 <= 16383);
 var_1_11 = __VERIFIER_nondet_short();
 assume_abort_if_not(var_1_11 >= -8191);
 assume_abort_if_not(var_1_11 <= 8192);
 var_1_12 = __VERIFIER_nondet_short();
 assume_abort_if_not(var_1_12 >= -8191);
 assume_abort_if_not(var_1_12 <= 8191);
 var_1_13 = __VERIFIER_nondet_short();
 assume_abort_if_not(var_1_13 >= 0);
 assume_abort_if_not(var_1_13 <= 32766);
 var_1_16 = __VERIFIER_nondet_float();
 assume_abort_if_not((var_1_16 >= -922337.2036854765600e+13F && var_1_16 <= -1.0e-20F) || (var_1_16 <= 9223372.036854765600e+12F && var_1_16 >= 1.0e-20F ));
 var_1_17 = __VERIFIER_nondet_float();
 assume_abort_if_not((var_1_17 >= -922337.2036854765600e+13F && var_1_17 <= -1.0e-20F) || (var_1_17 <= 9223372.036854765600e+12F && var_1_17 >= 1.0e-20F ));
}
void updateLastVariables() {
 last_1_var_1_1 = var_1_1;
}
int property() {
 return ((((var_1_2 && var_1_3) ? ((var_1_2 && (var_1_14 > last_1_var_1_1)) ? (var_1_1 == ((signed long int) (var_1_6 - var_1_7))) : (var_1_1 == ((signed long int) var_1_6))) : 1) && ((var_1_14 > var_1_14) ? (var_1_8 == ((signed short int) ((var_1_9 - var_1_10) + ((((-4) < ((var_1_11 + var_1_12))) ? (-4) : ((var_1_11 + var_1_12))))))) : (var_1_8 == ((signed short int) (((((var_1_9) < (var_1_10)) ? (var_1_9) : (var_1_10))) - var_1_13))))) && (var_1_3 ? (var_1_14 == ((unsigned long int) (2931747731u - var_1_10))) : 1)) && ((var_1_11 >= var_1_1) ? (var_1_15 == ((float) ((((var_1_16) > (var_1_17)) ? (var_1_16) : (var_1_17))))) : 1)
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
