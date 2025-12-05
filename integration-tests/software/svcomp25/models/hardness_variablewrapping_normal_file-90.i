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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch90normal.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
signed short int var_1_1 = 25;
unsigned char var_1_2 = 1;
signed short int var_1_3 = 0;
signed short int var_1_4 = 1;
signed short int var_1_5 = 10;
unsigned long int var_1_6 = 2;
unsigned long int var_1_7 = 2762957886;
unsigned long int var_1_8 = 2;
unsigned char var_1_10 = 0;
unsigned char var_1_11 = 1;
unsigned char var_1_12 = 0;
unsigned char var_1_13 = 1;
signed short int var_1_14 = -25;
signed short int var_1_15 = 10;
signed long int var_1_16 = -5;
unsigned char last_1_var_1_10 = 0;
signed short int last_1_var_1_14 = -25;
signed long int last_1_var_1_16 = -5;
void initially(void) {
}
void step(void) {
 unsigned long int stepLocal_1 = var_1_7 - var_1_8;
 signed long int stepLocal_0 = (((var_1_3) < (var_1_5)) ? (var_1_3) : (var_1_5));
 if (last_1_var_1_14 != stepLocal_0) {
  if (stepLocal_1 >= last_1_var_1_16) {
   if (last_1_var_1_10) {
    var_1_6 = var_1_8;
   } else {
    var_1_6 = var_1_8;
   }
  } else {
   var_1_6 = var_1_8;
  }
 } else {
  var_1_6 = var_1_8;
 }
 if (var_1_6 <= var_1_7) {
  if (var_1_15 > var_1_6) {
   var_1_16 = var_1_15;
  }
 }
 if (var_1_2) {
  var_1_10 = (var_1_11 || (! var_1_12));
 } else {
  var_1_10 = ((! var_1_13) || var_1_12);
 }
 var_1_14 = ((((var_1_3) > ((var_1_15 - 256))) ? (var_1_3) : ((var_1_15 - 256))));
 if (var_1_10) {
  var_1_1 = (((((var_1_3 + var_1_4)) < (var_1_5)) ? ((var_1_3 + var_1_4)) : (var_1_5)));
 }
}
void updateVariables() {
 var_1_2 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_2 >= 0);
 assume_abort_if_not(var_1_2 <= 1);
 var_1_3 = __VERIFIER_nondet_short();
 assume_abort_if_not(var_1_3 >= -16383);
 assume_abort_if_not(var_1_3 <= 16383);
 var_1_4 = __VERIFIER_nondet_short();
 assume_abort_if_not(var_1_4 >= -16383);
 assume_abort_if_not(var_1_4 <= 16383);
 var_1_5 = __VERIFIER_nondet_short();
 assume_abort_if_not(var_1_5 >= -32767);
 assume_abort_if_not(var_1_5 <= 32766);
 var_1_7 = __VERIFIER_nondet_ulong();
 assume_abort_if_not(var_1_7 >= 2147483647);
 assume_abort_if_not(var_1_7 <= 4294967295);
 var_1_8 = __VERIFIER_nondet_ulong();
 assume_abort_if_not(var_1_8 >= 0);
 assume_abort_if_not(var_1_8 <= 2147483647);
 var_1_11 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_11 >= 0);
 assume_abort_if_not(var_1_11 <= 1);
 var_1_12 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_12 >= 0);
 assume_abort_if_not(var_1_12 <= 0);
 var_1_13 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_13 >= 1);
 assume_abort_if_not(var_1_13 <= 1);
 var_1_15 = __VERIFIER_nondet_short();
 assume_abort_if_not(var_1_15 >= -1);
 assume_abort_if_not(var_1_15 <= 32766);
}
void updateLastVariables() {
 last_1_var_1_10 = var_1_10;
 last_1_var_1_14 = var_1_14;
 last_1_var_1_16 = var_1_16;
}
int property() {
 return ((((var_1_10 ? (var_1_1 == ((signed short int) (((((var_1_3 + var_1_4)) < (var_1_5)) ? ((var_1_3 + var_1_4)) : (var_1_5))))) : 1) && ((last_1_var_1_14 != ((((var_1_3) < (var_1_5)) ? (var_1_3) : (var_1_5)))) ? (((var_1_7 - var_1_8) >= last_1_var_1_16) ? (last_1_var_1_10 ? (var_1_6 == ((unsigned long int) var_1_8)) : (var_1_6 == ((unsigned long int) var_1_8))) : (var_1_6 == ((unsigned long int) var_1_8))) : (var_1_6 == ((unsigned long int) var_1_8)))) && (var_1_2 ? (var_1_10 == ((unsigned char) (var_1_11 || (! var_1_12)))) : (var_1_10 == ((unsigned char) ((! var_1_13) || var_1_12))))) && (var_1_14 == ((signed short int) ((((var_1_3) > ((var_1_15 - 256))) ? (var_1_3) : ((var_1_15 - 256))))))) && ((var_1_6 <= var_1_7) ? ((var_1_15 > var_1_6) ? (var_1_16 == ((signed long int) var_1_15)) : 1) : 1)
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
