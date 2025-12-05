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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch3325_while.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
signed short int var_1_1 = -10;
unsigned char var_1_7 = 200;
unsigned char var_1_8 = 4;
signed char var_1_9 = 50;
signed char var_1_12 = -5;
float var_1_13 = 999999999999.8;
float var_1_14 = 100.5;
float var_1_15 = 32.75;
unsigned char var_1_16 = 1;
unsigned char var_1_17 = 1;
unsigned char var_1_18 = 128;
unsigned char last_1_var_1_7 = 200;
signed char last_1_var_1_9 = 50;
void initially(void) {
}
void step(void) {
 signed long int stepLocal_0 = (last_1_var_1_9 ^ last_1_var_1_9) + last_1_var_1_9;
 if (stepLocal_0 < -1) {
  var_1_1 = 8;
 } else {
  var_1_1 = (128 - (last_1_var_1_7 + last_1_var_1_7));
 }
 var_1_16 = var_1_17;
 var_1_18 = var_1_8;
 if (var_1_18 == var_1_18) {
  var_1_7 = var_1_8;
 }
 signed short int stepLocal_3 = var_1_1;
 if (var_1_18 == stepLocal_3) {
  var_1_13 = (var_1_14 - var_1_15);
 }
 signed short int stepLocal_2 = var_1_1;
 unsigned char stepLocal_1 = (var_1_1 * var_1_18) < -10000;
 if (var_1_16) {
  if (stepLocal_1 && var_1_16) {
   if (stepLocal_2 > var_1_1) {
    var_1_9 = var_1_12;
   }
  }
 }
}
void updateVariables() {
 var_1_8 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_8 >= 0);
 assume_abort_if_not(var_1_8 <= 254);
 var_1_12 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_12 >= -127);
 assume_abort_if_not(var_1_12 <= 126);
 var_1_14 = __VERIFIER_nondet_float();
 assume_abort_if_not((var_1_14 >= 0.0F && var_1_14 <= -1.0e-20F) || (var_1_14 <= 9223372.036854765600e+12F && var_1_14 >= 1.0e-20F ));
 var_1_15 = __VERIFIER_nondet_float();
 assume_abort_if_not((var_1_15 >= 0.0F && var_1_15 <= -1.0e-20F) || (var_1_15 <= 9223372.036854765600e+12F && var_1_15 >= 1.0e-20F ));
 var_1_17 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_17 >= 1);
 assume_abort_if_not(var_1_17 <= 1);
}
void updateLastVariables() {
 last_1_var_1_7 = var_1_7;
 last_1_var_1_9 = var_1_9;
}
int property() {
 return ((((((((last_1_var_1_9 ^ last_1_var_1_9) + last_1_var_1_9) < -1) ? (var_1_1 == ((signed short int) 8)) : (var_1_1 == ((signed short int) (128 - (last_1_var_1_7 + last_1_var_1_7))))) && ((var_1_18 == var_1_18) ? (var_1_7 == ((unsigned char) var_1_8)) : 1)) && (var_1_16 ? ((((var_1_1 * var_1_18) < -10000) && var_1_16) ? ((var_1_1 > var_1_1) ? (var_1_9 == ((signed char) var_1_12)) : 1) : 1) : 1)) && ((var_1_18 == var_1_1) ? (var_1_13 == ((float) (var_1_14 - var_1_15))) : 1)) && (var_1_16 == ((unsigned char) var_1_17))) && (var_1_18 == ((unsigned char) var_1_8))
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
