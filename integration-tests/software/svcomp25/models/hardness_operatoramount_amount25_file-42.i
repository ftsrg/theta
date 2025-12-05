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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch42Amount25.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
signed long int var_1_1 = -1;
unsigned char var_1_6 = 10;
unsigned char var_1_7 = 128;
unsigned char var_1_8 = 1;
float var_1_9 = 9999999999.5;
unsigned char var_1_10 = 0;
unsigned char var_1_11 = 1;
unsigned char var_1_12 = 0;
unsigned char var_1_13 = 0;
unsigned char var_1_14 = 0;
unsigned char var_1_15 = 0;
signed long int var_1_16 = 16;
unsigned char var_1_17 = 1;
signed long int last_1_var_1_1 = -1;
void initially(void) {
}
void step(void) {
 if (last_1_var_1_1 >= -1000) {
  var_1_6 = (var_1_7 - 100);
 }
 var_1_16 = var_1_6;
 var_1_17 = var_1_7;
 if (var_1_16 > var_1_6) {
  var_1_1 = (((((var_1_17) < (var_1_17)) ? (var_1_17) : (var_1_17))) - 10);
 } else {
  var_1_1 = var_1_17;
 }
 unsigned char stepLocal_1 = 49.5f <= var_1_9;
 unsigned char stepLocal_0 = var_1_17;
 if (stepLocal_1 && (var_1_10 && var_1_11)) {
  if (var_1_6 < stepLocal_0) {
   var_1_8 = (var_1_11 || var_1_12);
  } else {
   var_1_8 = (! (var_1_13 || (var_1_14 || var_1_15)));
  }
 } else {
  var_1_8 = var_1_12;
 }
}
void updateVariables() {
 var_1_7 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_7 >= 127);
 assume_abort_if_not(var_1_7 <= 254);
 var_1_9 = __VERIFIER_nondet_float();
 assume_abort_if_not((var_1_9 >= -922337.2036854776000e+13F && var_1_9 <= -1.0e-20F) || (var_1_9 <= 9223372.036854776000e+12F && var_1_9 >= 1.0e-20F ));
 var_1_10 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_10 >= 0);
 assume_abort_if_not(var_1_10 <= 1);
 var_1_11 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_11 >= 0);
 assume_abort_if_not(var_1_11 <= 1);
 var_1_12 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_12 >= 1);
 assume_abort_if_not(var_1_12 <= 1);
 var_1_13 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_13 >= 0);
 assume_abort_if_not(var_1_13 <= 0);
 var_1_14 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_14 >= 0);
 assume_abort_if_not(var_1_14 <= 0);
 var_1_15 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_15 >= 0);
 assume_abort_if_not(var_1_15 <= 0);
}
void updateLastVariables() {
 last_1_var_1_1 = var_1_1;
}
int property() {
 return (((((var_1_16 > var_1_6) ? (var_1_1 == ((signed long int) (((((var_1_17) < (var_1_17)) ? (var_1_17) : (var_1_17))) - 10))) : (var_1_1 == ((signed long int) var_1_17))) && ((last_1_var_1_1 >= -1000) ? (var_1_6 == ((unsigned char) (var_1_7 - 100))) : 1)) && (((49.5f <= var_1_9) && (var_1_10 && var_1_11)) ? ((var_1_6 < var_1_17) ? (var_1_8 == ((unsigned char) (var_1_11 || var_1_12))) : (var_1_8 == ((unsigned char) (! (var_1_13 || (var_1_14 || var_1_15)))))) : (var_1_8 == ((unsigned char) var_1_12)))) && (var_1_16 == ((signed long int) var_1_6))) && (var_1_17 == ((unsigned char) var_1_7))
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
