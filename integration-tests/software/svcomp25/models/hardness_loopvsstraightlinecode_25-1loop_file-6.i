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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch625_1loop.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
unsigned long int var_1_1 = 0;
unsigned short int var_1_4 = 32;
unsigned short int var_1_6 = 10;
signed long int var_1_7 = 4;
double var_1_9 = 8.125;
double var_1_10 = 1.75;
unsigned short int var_1_11 = 128;
unsigned char var_1_12 = 0;
unsigned char var_1_13 = 0;
unsigned char var_1_14 = 0;
unsigned char var_1_15 = 0;
unsigned char var_1_16 = 0;
unsigned char var_1_17 = 1;
signed long int var_1_18 = 16;
unsigned long int last_1_var_1_1 = 0;
unsigned short int last_1_var_1_6 = 10;
signed long int last_1_var_1_18 = 16;
void initially(void) {
}
void step(void) {
 signed long int stepLocal_1 = last_1_var_1_6;
 signed long int stepLocal_0 = last_1_var_1_18;
 if ((((((last_1_var_1_1) > (last_1_var_1_6)) ? (last_1_var_1_1) : (last_1_var_1_6))) / var_1_4) > stepLocal_0) {
  if (last_1_var_1_18 == stepLocal_1) {
   var_1_1 = 1000000000u;
  } else {
   var_1_1 = 128u;
  }
 }
 if ((var_1_4 - var_1_1) == var_1_1) {
  if ((var_1_9 - 255.5) > var_1_10) {
   var_1_6 = var_1_11;
  }
 } else {
  var_1_6 = var_1_11;
 }
 if ((var_1_6 * (var_1_7 + var_1_6)) > var_1_1) {
  var_1_18 = var_1_6;
 }
 if (var_1_13) {
  var_1_12 = ((var_1_14 || var_1_15) || var_1_16);
 } else {
  var_1_12 = var_1_17;
 }
}
void updateVariables() {
 var_1_4 = __VERIFIER_nondet_ushort();
 assume_abort_if_not(var_1_4 >= 0);
 assume_abort_if_not(var_1_4 <= 65535);
 assume_abort_if_not(var_1_4 != 0);
 var_1_7 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_7 >= 0);
 assume_abort_if_not(var_1_7 <= 17);
 var_1_9 = __VERIFIER_nondet_double();
 assume_abort_if_not((var_1_9 >= 0.0F && var_1_9 <= -1.0e-20F) || (var_1_9 <= 9223372.036854776000e+12F && var_1_9 >= 1.0e-20F ));
 var_1_10 = __VERIFIER_nondet_double();
 assume_abort_if_not((var_1_10 >= -922337.2036854776000e+13F && var_1_10 <= -1.0e-20F) || (var_1_10 <= 9223372.036854776000e+12F && var_1_10 >= 1.0e-20F ));
 var_1_11 = __VERIFIER_nondet_ushort();
 assume_abort_if_not(var_1_11 >= 0);
 assume_abort_if_not(var_1_11 <= 65534);
 var_1_13 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_13 >= 0);
 assume_abort_if_not(var_1_13 <= 1);
 var_1_14 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_14 >= 0);
 assume_abort_if_not(var_1_14 <= 0);
 var_1_15 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_15 >= 0);
 assume_abort_if_not(var_1_15 <= 0);
 var_1_16 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_16 >= 0);
 assume_abort_if_not(var_1_16 <= 0);
 var_1_17 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_17 >= 1);
 assume_abort_if_not(var_1_17 <= 1);
}
void updateLastVariables() {
 last_1_var_1_1 = var_1_1;
 last_1_var_1_6 = var_1_6;
 last_1_var_1_18 = var_1_18;
}
int property() {
 return (((((((((last_1_var_1_1) > (last_1_var_1_6)) ? (last_1_var_1_1) : (last_1_var_1_6))) / var_1_4) > last_1_var_1_18) ? ((last_1_var_1_18 == last_1_var_1_6) ? (var_1_1 == ((unsigned long int) 1000000000u)) : (var_1_1 == ((unsigned long int) 128u))) : 1) && (((var_1_4 - var_1_1) == var_1_1) ? (((var_1_9 - 255.5) > var_1_10) ? (var_1_6 == ((unsigned short int) var_1_11)) : 1) : (var_1_6 == ((unsigned short int) var_1_11)))) && (var_1_13 ? (var_1_12 == ((unsigned char) ((var_1_14 || var_1_15) || var_1_16))) : (var_1_12 == ((unsigned char) var_1_17)))) && (((var_1_6 * (var_1_7 + var_1_6)) > var_1_1) ? (var_1_18 == ((signed long int) var_1_6)) : 1)
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
