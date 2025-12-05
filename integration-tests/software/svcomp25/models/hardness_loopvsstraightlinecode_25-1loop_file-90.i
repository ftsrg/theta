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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch9025_1loop.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
signed short int var_1_1 = 25;
unsigned long int var_1_6 = 2;
unsigned long int var_1_7 = 2762957886;
unsigned long int var_1_8 = 2;
unsigned long int var_1_9 = 1000000000;
unsigned long int var_1_10 = 100;
signed char var_1_11 = 4;
signed char var_1_12 = 8;
signed char var_1_13 = 10;
signed char var_1_14 = 8;
unsigned char var_1_15 = 1;
unsigned char var_1_16 = 0;
double var_1_17 = 32.4;
double var_1_18 = 15.5;
unsigned long int last_1_var_1_6 = 2;
void initially(void) {
}
void step(void) {
 var_1_15 = var_1_16;
 var_1_17 = var_1_18;
 if (var_1_15) {
  var_1_11 = (((var_1_12 + var_1_13) + var_1_14) - 50);
 }
 if (var_1_15) {
  var_1_1 = (((((var_1_11 + var_1_11)) < (var_1_11)) ? ((var_1_11 + var_1_11)) : (var_1_11)));
 }
 signed long int stepLocal_2 = (((var_1_11) < (var_1_11)) ? (var_1_11) : (var_1_11));
 signed long int stepLocal_1 = (((var_1_11) > (var_1_11)) ? (var_1_11) : (var_1_11));
 unsigned long int stepLocal_0 = var_1_7 - var_1_8;
 if (last_1_var_1_6 != stepLocal_2) {
  if (stepLocal_0 >= var_1_9) {
   if (stepLocal_1 < (var_1_8 >> var_1_9)) {
    var_1_6 = var_1_8;
   } else {
    var_1_6 = var_1_10;
   }
  } else {
   var_1_6 = var_1_10;
  }
 } else {
  var_1_6 = var_1_8;
 }
}
void updateVariables() {
 var_1_7 = __VERIFIER_nondet_ulong();
 assume_abort_if_not(var_1_7 >= 2147483647);
 assume_abort_if_not(var_1_7 <= 4294967295);
 var_1_8 = __VERIFIER_nondet_ulong();
 assume_abort_if_not(var_1_8 >= 0);
 assume_abort_if_not(var_1_8 <= 2147483647);
 var_1_9 = __VERIFIER_nondet_ulong();
 assume_abort_if_not(var_1_9 >= 0);
 assume_abort_if_not(var_1_9 <= 4294967295);
 var_1_10 = __VERIFIER_nondet_ulong();
 assume_abort_if_not(var_1_10 >= 0);
 assume_abort_if_not(var_1_10 <= 4294967294);
 var_1_12 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_12 >= 0);
 assume_abort_if_not(var_1_12 <= 32);
 var_1_13 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_13 >= 0);
 assume_abort_if_not(var_1_13 <= 31);
 var_1_14 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_14 >= 0);
 assume_abort_if_not(var_1_14 <= 63);
 var_1_16 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_16 >= 1);
 assume_abort_if_not(var_1_16 <= 1);
 var_1_18 = __VERIFIER_nondet_double();
 assume_abort_if_not((var_1_18 >= -922337.2036854765600e+13F && var_1_18 <= -1.0e-20F) || (var_1_18 <= 9223372.036854765600e+12F && var_1_18 >= 1.0e-20F ));
}
void updateLastVariables() {
 last_1_var_1_6 = var_1_6;
}
int property() {
 return ((((var_1_15 ? (var_1_1 == ((signed short int) (((((var_1_11 + var_1_11)) < (var_1_11)) ? ((var_1_11 + var_1_11)) : (var_1_11))))) : 1) && ((last_1_var_1_6 != ((((var_1_11) < (var_1_11)) ? (var_1_11) : (var_1_11)))) ? (((var_1_7 - var_1_8) >= var_1_9) ? ((((((var_1_11) > (var_1_11)) ? (var_1_11) : (var_1_11))) < (var_1_8 >> var_1_9)) ? (var_1_6 == ((unsigned long int) var_1_8)) : (var_1_6 == ((unsigned long int) var_1_10))) : (var_1_6 == ((unsigned long int) var_1_10))) : (var_1_6 == ((unsigned long int) var_1_8)))) && (var_1_15 ? (var_1_11 == ((signed char) (((var_1_12 + var_1_13) + var_1_14) - 50))) : 1)) && (var_1_15 == ((unsigned char) var_1_16))) && (var_1_17 == ((double) var_1_18))
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
