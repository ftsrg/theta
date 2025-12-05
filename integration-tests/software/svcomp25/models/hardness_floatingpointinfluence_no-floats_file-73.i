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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch73no_floats.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
signed long int var_1_1 = 5;
unsigned char var_1_6 = 1;
signed long int var_1_7 = 0;
unsigned char var_1_8 = 25;
unsigned char var_1_9 = 100;
unsigned char var_1_10 = 1;
signed long int var_1_12 = 15;
signed long int var_1_13 = 1;
unsigned char var_1_14 = 0;
unsigned char var_1_15 = 0;
signed long int var_1_16 = 16;
signed char var_1_17 = 10;
signed char var_1_18 = -10;
signed long int var_1_19 = -16;
signed long int last_1_var_1_12 = 15;
void initially(void) {
}
void step(void) {
 if (var_1_6) {
  var_1_8 = ((((var_1_9) > (var_1_10)) ? (var_1_9) : (var_1_10)));
 } else {
  if (last_1_var_1_12 < (last_1_var_1_12 + var_1_7)) {
   var_1_8 = ((((var_1_9) < (var_1_10)) ? (var_1_9) : (var_1_10)));
  }
 }
 var_1_19 = var_1_8;
 if (var_1_19 > var_1_9) {
  if (var_1_6) {
   var_1_12 = (var_1_13 - ((((99999.25f) < 0 ) ? -(99999.25f) : (99999.25f))));
  } else {
   if (var_1_14 && var_1_15) {
    var_1_12 = (var_1_13 - var_1_16);
   } else {
    var_1_12 = var_1_16;
   }
  }
 } else {
  var_1_12 = var_1_13;
 }
 signed long int stepLocal_0 = (((var_1_8) > ((var_1_8 + var_1_19))) ? (var_1_8) : ((var_1_8 + var_1_19)));
 if (var_1_8 <= stepLocal_0) {
  if (! var_1_6) {
   var_1_1 = var_1_7;
  } else {
   var_1_1 = var_1_7;
  }
 }
 var_1_17 = var_1_18;
}
void updateVariables() {
 var_1_6 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_6 >= 0);
 assume_abort_if_not(var_1_6 <= 1);
 var_1_7 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_7 >= -2147483648);
 assume_abort_if_not(var_1_7 <= 2147483647);
 var_1_9 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_9 >= 0);
 assume_abort_if_not(var_1_9 <= 254);
 var_1_10 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_10 >= 0);
 assume_abort_if_not(var_1_10 <= 254);
 var_1_13 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_13 >= 0);
 assume_abort_if_not(var_1_13 <= 2147483647);
 var_1_14 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_14 >= 0);
 assume_abort_if_not(var_1_14 <= 1);
 var_1_15 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_15 >= 0);
 assume_abort_if_not(var_1_15 <= 1);
 var_1_16 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_16 >= 0);
 assume_abort_if_not(var_1_16 <= 2147483647);
 var_1_18 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_18 >= -127);
 assume_abort_if_not(var_1_18 <= 126);
}
void updateLastVariables() {
 last_1_var_1_12 = var_1_12;
}
int property() {
 return (((((var_1_8 <= ((((var_1_8) > ((var_1_8 + var_1_19))) ? (var_1_8) : ((var_1_8 + var_1_19))))) ? ((! var_1_6) ? (var_1_1 == ((signed long int) var_1_7)) : (var_1_1 == ((signed long int) var_1_7))) : 1) && (var_1_6 ? (var_1_8 == ((unsigned char) ((((var_1_9) > (var_1_10)) ? (var_1_9) : (var_1_10))))) : ((last_1_var_1_12 < (last_1_var_1_12 + var_1_7)) ? (var_1_8 == ((unsigned char) ((((var_1_9) < (var_1_10)) ? (var_1_9) : (var_1_10))))) : 1))) && ((var_1_19 > var_1_9) ? (var_1_6 ? (var_1_12 == ((signed long int) (var_1_13 - ((((99999.25f) < 0 ) ? -(99999.25f) : (99999.25f)))))) : ((var_1_14 && var_1_15) ? (var_1_12 == ((signed long int) (var_1_13 - var_1_16))) : (var_1_12 == ((signed long int) var_1_16)))) : (var_1_12 == ((signed long int) var_1_13)))) && (var_1_17 == ((signed char) var_1_18))) && (var_1_19 == ((signed long int) var_1_8))
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
