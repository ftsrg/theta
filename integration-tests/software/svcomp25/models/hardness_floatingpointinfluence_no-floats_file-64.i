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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch64no_floats.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
signed long int var_1_1 = 0;
unsigned long int var_1_2 = 128;
unsigned long int var_1_3 = 2941876006;
unsigned long int var_1_5 = 256;
signed long int var_1_6 = 63;
signed long int var_1_7 = 0;
signed long int var_1_8 = 0;
signed long int var_1_9 = 9;
unsigned char var_1_10 = 0;
unsigned char var_1_11 = 0;
unsigned char var_1_12 = 0;
signed short int var_1_13 = -2;
unsigned char var_1_16 = 10;
unsigned short int var_1_17 = 8;
unsigned char var_1_18 = 16;
unsigned char last_1_var_1_16 = 10;
void initially(void) {
}
void step(void) {
 signed long int stepLocal_1 = last_1_var_1_16;
 unsigned long int stepLocal_0 = var_1_3;
 if (stepLocal_1 <= (var_1_3 - last_1_var_1_16)) {
  if (stepLocal_0 < (((((last_1_var_1_16 / var_1_5)) > (last_1_var_1_16)) ? ((last_1_var_1_16 / var_1_5)) : (last_1_var_1_16)))) {
   if ((var_1_6 + var_1_7) > var_1_8) {
    var_1_1 = var_1_9;
   }
  } else {
   var_1_1 = var_1_9;
  }
 }
 if (var_1_1 < var_1_1) {
  var_1_10 = (! (var_1_11 && var_1_12));
 }
 unsigned long int stepLocal_2 = var_1_2 & (var_1_5 / var_1_17);
 if (stepLocal_2 > var_1_3) {
  if (! var_1_10) {
   var_1_16 = var_1_18;
  } else {
   var_1_16 = var_1_18;
  }
 } else {
  var_1_16 = var_1_18;
 }
 if (var_1_10) {
  if (var_1_12 || (var_1_1 < (var_1_1 * var_1_1))) {
   var_1_13 = (var_1_16 + var_1_16);
  }
 }
}
void updateVariables() {
 var_1_2 = __VERIFIER_nondet_ulong();
 assume_abort_if_not(var_1_2 >= 0);
 assume_abort_if_not(var_1_2 <= 4294967295);
 var_1_3 = __VERIFIER_nondet_ulong();
 assume_abort_if_not(var_1_3 >= 2147483647);
 assume_abort_if_not(var_1_3 <= 4294967295);
 var_1_5 = __VERIFIER_nondet_ulong();
 assume_abort_if_not(var_1_5 >= 0);
 assume_abort_if_not(var_1_5 <= 4294967295);
 assume_abort_if_not(var_1_5 != 0);
 var_1_6 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_6 >= -2147483648);
 assume_abort_if_not(var_1_6 <= 2147483647);
 var_1_7 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_7 >= -2147483648);
 assume_abort_if_not(var_1_7 <= 2147483647);
 var_1_8 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_8 >= -2147483648);
 assume_abort_if_not(var_1_8 <= 2147483647);
 var_1_9 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_9 >= -2147483648);
 assume_abort_if_not(var_1_9 <= 2147483647);
 var_1_11 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_11 >= 1);
 assume_abort_if_not(var_1_11 <= 1);
 var_1_12 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_12 >= 1);
 assume_abort_if_not(var_1_12 <= 1);
 var_1_17 = __VERIFIER_nondet_ushort();
 assume_abort_if_not(var_1_17 >= 0);
 assume_abort_if_not(var_1_17 <= 65535);
 assume_abort_if_not(var_1_17 != 0);
 var_1_18 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_18 >= 0);
 assume_abort_if_not(var_1_18 <= 254);
}
void updateLastVariables() {
 last_1_var_1_16 = var_1_16;
}
int property() {
 return ((((last_1_var_1_16 <= (var_1_3 - last_1_var_1_16)) ? ((var_1_3 < (((((last_1_var_1_16 / var_1_5)) > (last_1_var_1_16)) ? ((last_1_var_1_16 / var_1_5)) : (last_1_var_1_16)))) ? (((var_1_6 + var_1_7) > var_1_8) ? (var_1_1 == ((signed long int) var_1_9)) : 1) : (var_1_1 == ((signed long int) var_1_9))) : 1) && ((var_1_1 < var_1_1) ? (var_1_10 == ((unsigned char) (! (var_1_11 && var_1_12)))) : 1)) && (var_1_10 ? ((var_1_12 || (var_1_1 < (var_1_1 * var_1_1))) ? (var_1_13 == ((signed short int) (var_1_16 + var_1_16))) : 1) : 1)) && (((var_1_2 & (var_1_5 / var_1_17)) > var_1_3) ? ((! var_1_10) ? (var_1_16 == ((unsigned char) var_1_18)) : (var_1_16 == ((unsigned char) var_1_18))) : (var_1_16 == ((unsigned char) var_1_18)))
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
