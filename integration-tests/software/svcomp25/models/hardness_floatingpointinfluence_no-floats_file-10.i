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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch10no_floats.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
unsigned long int var_1_1 = 5;
unsigned long int var_1_2 = 8;
signed long int var_1_3 = 9;
signed long int var_1_6 = 1000000;
signed long int var_1_7 = 49;
signed long int var_1_8 = 0;
signed char var_1_9 = -10;
unsigned short int var_1_10 = 58996;
unsigned short int var_1_11 = 32;
signed char var_1_12 = 32;
signed char var_1_13 = 16;
signed char var_1_14 = 2;
signed long int var_1_15 = 32;
signed long int var_1_17 = 1000000000;
signed long int var_1_18 = 0;
signed char var_1_19 = 2;
unsigned char var_1_20 = 0;
unsigned char var_1_21 = 0;
signed long int last_1_var_1_3 = 9;
void initially(void) {
}
void step(void) {
 var_1_1 = var_1_2;
 var_1_18 = var_1_8;
 var_1_19 = var_1_12;
 var_1_20 = var_1_21;
 signed char stepLocal_1 = var_1_19;
 if ((- (var_1_10 - var_1_11)) >= stepLocal_1) {
  var_1_9 = (var_1_12 - ((((var_1_13) > (var_1_14)) ? (var_1_13) : (var_1_14))));
 } else {
  var_1_9 = ((((var_1_12) < (var_1_14)) ? (var_1_12) : (var_1_14)));
 }
 if (var_1_20) {
  var_1_15 = (var_1_12 - var_1_14);
 } else {
  var_1_15 = (var_1_13 - ((var_1_17 - 4) + ((((var_1_11) < 0 ) ? -(var_1_11) : (var_1_11)))));
 }
 signed long int stepLocal_0 = var_1_15;
 if (stepLocal_0 < var_1_1) {
  var_1_3 = -0.5;
 } else {
  if ((- last_1_var_1_3) == (var_1_6 - var_1_7)) {
   var_1_3 = var_1_8;
  } else {
   var_1_3 = var_1_8;
  }
 }
}
void updateVariables() {
 var_1_2 = __VERIFIER_nondet_ulong();
 assume_abort_if_not(var_1_2 >= 0);
 assume_abort_if_not(var_1_2 <= 4294967294);
 var_1_6 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_6 >= 0);
 assume_abort_if_not(var_1_6 <= 2147483647);
 var_1_7 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_7 >= 0);
 assume_abort_if_not(var_1_7 <= 2147483647);
 var_1_8 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_8 >= -2147483648);
 assume_abort_if_not(var_1_8 <= 2147483647);
 var_1_10 = __VERIFIER_nondet_ushort();
 assume_abort_if_not(var_1_10 >= 32767);
 assume_abort_if_not(var_1_10 <= 65535);
 var_1_11 = __VERIFIER_nondet_ushort();
 assume_abort_if_not(var_1_11 >= 0);
 assume_abort_if_not(var_1_11 <= 32767);
 var_1_12 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_12 >= -1);
 assume_abort_if_not(var_1_12 <= 126);
 var_1_13 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_13 >= 0);
 assume_abort_if_not(var_1_13 <= 126);
 var_1_14 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_14 >= 0);
 assume_abort_if_not(var_1_14 <= 126);
 var_1_17 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_17 >= 536870911);
 assume_abort_if_not(var_1_17 <= 1073741823);
 var_1_21 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_21 >= 1);
 assume_abort_if_not(var_1_21 <= 1);
}
void updateLastVariables() {
 last_1_var_1_3 = var_1_3;
}
int property() {
 return ((((((var_1_1 == ((unsigned long int) var_1_2)) && ((var_1_15 < var_1_1) ? (var_1_3 == ((signed long int) -0.5)) : (((- last_1_var_1_3) == (var_1_6 - var_1_7)) ? (var_1_3 == ((signed long int) var_1_8)) : (var_1_3 == ((signed long int) var_1_8))))) && (((- (var_1_10 - var_1_11)) >= var_1_19) ? (var_1_9 == ((signed char) (var_1_12 - ((((var_1_13) > (var_1_14)) ? (var_1_13) : (var_1_14)))))) : (var_1_9 == ((signed char) ((((var_1_12) < (var_1_14)) ? (var_1_12) : (var_1_14))))))) && (var_1_20 ? (var_1_15 == ((signed long int) (var_1_12 - var_1_14))) : (var_1_15 == ((signed long int) (var_1_13 - ((var_1_17 - 4) + ((((var_1_11) < 0 ) ? -(var_1_11) : (var_1_11))))))))) && (var_1_18 == ((signed long int) var_1_8))) && (var_1_19 == ((signed char) var_1_12))) && (var_1_20 == ((unsigned char) var_1_21))
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
