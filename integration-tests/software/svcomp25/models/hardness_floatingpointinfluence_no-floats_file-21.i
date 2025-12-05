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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch21no_floats.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
unsigned short int var_1_1 = 32;
unsigned char var_1_7 = 0;
signed long int var_1_8 = 15;
signed long int var_1_9 = 15;
signed long int var_1_10 = 32;
unsigned char var_1_12 = 1;
signed short int var_1_13 = 256;
signed long int var_1_14 = 5;
signed long int var_1_15 = 8;
unsigned char last_1_var_1_7 = 0;
signed short int last_1_var_1_13 = 256;
void initially(void) {
}
void step(void) {
 if ((last_1_var_1_13 + ((((last_1_var_1_13) > (last_1_var_1_13)) ? (last_1_var_1_13) : (last_1_var_1_13)))) < (last_1_var_1_13 * last_1_var_1_13)) {
  if (last_1_var_1_13 < (last_1_var_1_13 - last_1_var_1_13)) {
   if (last_1_var_1_13 != (((((((last_1_var_1_13) < (last_1_var_1_13)) ? (last_1_var_1_13) : (last_1_var_1_13))) < 0 ) ? -((((last_1_var_1_13) < (last_1_var_1_13)) ? (last_1_var_1_13) : (last_1_var_1_13))) : ((((last_1_var_1_13) < (last_1_var_1_13)) ? (last_1_var_1_13) : (last_1_var_1_13)))))) {
    var_1_1 = last_1_var_1_13;
   }
  }
 } else {
  var_1_1 = last_1_var_1_13;
 }
 if (var_1_12) {
  if ((var_1_14 - var_1_15) >= ((var_1_8 + var_1_10) + var_1_9)) {
   var_1_13 = ((((var_1_1) > (var_1_1)) ? (var_1_1) : (var_1_1)));
  } else {
   var_1_13 = var_1_1;
  }
 }
 if (((((var_1_8) < (var_1_9)) ? (var_1_8) : (var_1_9))) <= var_1_10) {
  if (last_1_var_1_7 && (var_1_1 >= var_1_1)) {
   var_1_7 = 0;
  }
 } else {
  var_1_7 = var_1_12;
 }
}
void updateVariables() {
 var_1_8 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_8 >= -2147483648);
 assume_abort_if_not(var_1_8 <= 2147483647);
 var_1_9 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_9 >= -2147483648);
 assume_abort_if_not(var_1_9 <= 2147483647);
 var_1_10 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_10 >= -2147483648);
 assume_abort_if_not(var_1_10 <= 2147483647);
 var_1_12 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_12 >= 1);
 assume_abort_if_not(var_1_12 <= 1);
 var_1_14 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_14 >= 0);
 assume_abort_if_not(var_1_14 <= 2147483647);
 var_1_15 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_15 >= 0);
 assume_abort_if_not(var_1_15 <= 2147483647);
}
void updateLastVariables() {
 last_1_var_1_7 = var_1_7;
 last_1_var_1_13 = var_1_13;
}
int property() {
 return ((((last_1_var_1_13 + ((((last_1_var_1_13) > (last_1_var_1_13)) ? (last_1_var_1_13) : (last_1_var_1_13)))) < (last_1_var_1_13 * last_1_var_1_13)) ? ((last_1_var_1_13 < (last_1_var_1_13 - last_1_var_1_13)) ? ((last_1_var_1_13 != (((((((last_1_var_1_13) < (last_1_var_1_13)) ? (last_1_var_1_13) : (last_1_var_1_13))) < 0 ) ? -((((last_1_var_1_13) < (last_1_var_1_13)) ? (last_1_var_1_13) : (last_1_var_1_13))) : ((((last_1_var_1_13) < (last_1_var_1_13)) ? (last_1_var_1_13) : (last_1_var_1_13)))))) ? (var_1_1 == ((unsigned short int) last_1_var_1_13)) : 1) : 1) : (var_1_1 == ((unsigned short int) last_1_var_1_13))) && ((((((var_1_8) < (var_1_9)) ? (var_1_8) : (var_1_9))) <= var_1_10) ? ((last_1_var_1_7 && (var_1_1 >= var_1_1)) ? (var_1_7 == ((unsigned char) 0)) : 1) : (var_1_7 == ((unsigned char) var_1_12)))) && (var_1_12 ? (((var_1_14 - var_1_15) >= ((var_1_8 + var_1_10) + var_1_9)) ? (var_1_13 == ((signed short int) ((((var_1_1) > (var_1_1)) ? (var_1_1) : (var_1_1))))) : (var_1_13 == ((signed short int) var_1_1))) : 1)
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
