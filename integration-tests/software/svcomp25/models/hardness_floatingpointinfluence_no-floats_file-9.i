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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch9no_floats.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
unsigned char var_1_1 = 10;
unsigned char var_1_3 = 4;
unsigned char var_1_7 = 0;
signed short int var_1_8 = 100;
unsigned char var_1_9 = 32;
signed long int var_1_10 = 9;
signed long int var_1_11 = 0;
signed short int var_1_12 = 1;
signed long int var_1_14 = -16;
unsigned char last_1_var_1_1 = 10;
signed long int last_1_var_1_10 = 9;
signed short int last_1_var_1_12 = 1;
signed long int last_1_var_1_14 = -16;
void initially(void) {
}
void step(void) {
 unsigned char stepLocal_0 = last_1_var_1_10 > last_1_var_1_10;
 if (((last_1_var_1_12 + last_1_var_1_1) < 10) || stepLocal_0) {
  var_1_12 = ((((((var_1_3 + last_1_var_1_12) - ((((last_1_var_1_14) > (last_1_var_1_12)) ? (last_1_var_1_14) : (last_1_var_1_12))))) > (last_1_var_1_1)) ? (((var_1_3 + last_1_var_1_12) - ((((last_1_var_1_14) > (last_1_var_1_12)) ? (last_1_var_1_14) : (last_1_var_1_12))))) : (last_1_var_1_1)));
 } else {
  var_1_12 = last_1_var_1_12;
 }
 var_1_14 = var_1_12;
 if ((10 << var_1_12) < (var_1_3 * var_1_14)) {
  var_1_8 = (var_1_12 + var_1_14);
 }
 var_1_9 = 64;
 var_1_10 = var_1_11;
 if (var_1_12 <= 16) {
  var_1_1 = var_1_3;
 } else {
  if (((((var_1_10) > (var_1_10)) ? (var_1_10) : (var_1_10))) < var_1_10) {
   if (var_1_7) {
    var_1_1 = var_1_3;
   } else {
    var_1_1 = var_1_3;
   }
  } else {
   var_1_1 = var_1_3;
  }
 }
}
void updateVariables() {
 var_1_3 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_3 >= 0);
 assume_abort_if_not(var_1_3 <= 254);
 var_1_7 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_7 >= 0);
 assume_abort_if_not(var_1_7 <= 1);
 var_1_11 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_11 >= -2147483648);
 assume_abort_if_not(var_1_11 <= 2147483647);
}
void updateLastVariables() {
 last_1_var_1_1 = var_1_1;
 last_1_var_1_10 = var_1_10;
 last_1_var_1_12 = var_1_12;
 last_1_var_1_14 = var_1_14;
}
int property() {
 return ((((((var_1_12 <= 16) ? (var_1_1 == ((unsigned char) var_1_3)) : ((((((var_1_10) > (var_1_10)) ? (var_1_10) : (var_1_10))) < var_1_10) ? (var_1_7 ? (var_1_1 == ((unsigned char) var_1_3)) : (var_1_1 == ((unsigned char) var_1_3))) : (var_1_1 == ((unsigned char) var_1_3)))) && (((10 << var_1_12) < (var_1_3 * var_1_14)) ? (var_1_8 == ((signed short int) (var_1_12 + var_1_14))) : 1)) && (var_1_9 == ((unsigned char) 64))) && (var_1_10 == ((signed long int) var_1_11))) && ((((last_1_var_1_12 + last_1_var_1_1) < 10) || (last_1_var_1_10 > last_1_var_1_10)) ? (var_1_12 == ((signed short int) ((((((var_1_3 + last_1_var_1_12) - ((((last_1_var_1_14) > (last_1_var_1_12)) ? (last_1_var_1_14) : (last_1_var_1_12))))) > (last_1_var_1_1)) ? (((var_1_3 + last_1_var_1_12) - ((((last_1_var_1_14) > (last_1_var_1_12)) ? (last_1_var_1_14) : (last_1_var_1_12))))) : (last_1_var_1_1))))) : (var_1_12 == ((signed short int) last_1_var_1_12)))) && (var_1_14 == ((signed long int) var_1_12))
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
