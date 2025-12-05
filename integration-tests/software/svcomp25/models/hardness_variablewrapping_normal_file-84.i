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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch84normal.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
unsigned char var_1_1 = 128;
unsigned char var_1_4 = 25;
unsigned char var_1_5 = 64;
unsigned char var_1_6 = 8;
unsigned char var_1_7 = 0;
unsigned short int var_1_8 = 64;
unsigned char var_1_9 = 1;
unsigned short int var_1_10 = 27843;
signed short int var_1_11 = -4;
unsigned char var_1_13 = 128;
unsigned char var_1_14 = 5;
signed short int var_1_15 = 28020;
signed short int var_1_16 = 128;
float var_1_17 = 10000000000000.926;
float var_1_18 = 1000000.6;
unsigned short int last_1_var_1_8 = 64;
signed short int last_1_var_1_11 = -4;
void initially(void) {
}
void step(void) {
 signed long int stepLocal_0 = last_1_var_1_11;
 if (stepLocal_0 != last_1_var_1_8) {
  var_1_1 = (var_1_4 + ((((((((var_1_5) < (var_1_6)) ? (var_1_5) : (var_1_6)))) > (var_1_7)) ? (((((var_1_5) < (var_1_6)) ? (var_1_5) : (var_1_6)))) : (var_1_7))));
 } else {
  var_1_1 = var_1_4;
 }
 if (var_1_9) {
  var_1_8 = ((var_1_10 + 23103) - (32 + var_1_6));
 }
 if (! (var_1_5 > var_1_10)) {
  var_1_16 = (32 - 8);
 } else {
  var_1_16 = (var_1_13 - var_1_4);
 }
 var_1_17 = var_1_18;
 if (var_1_1 < var_1_16) {
  if (((- 8) / (var_1_13 - var_1_14)) >= var_1_6) {
   var_1_11 = (var_1_16 - (var_1_15 - var_1_14));
  }
 }
}
void updateVariables() {
 var_1_4 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_4 >= 0);
 assume_abort_if_not(var_1_4 <= 127);
 var_1_5 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_5 >= 0);
 assume_abort_if_not(var_1_5 <= 127);
 var_1_6 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_6 >= 0);
 assume_abort_if_not(var_1_6 <= 127);
 var_1_7 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_7 >= 0);
 assume_abort_if_not(var_1_7 <= 127);
 var_1_9 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_9 >= 0);
 assume_abort_if_not(var_1_9 <= 1);
 var_1_10 = __VERIFIER_nondet_ushort();
 assume_abort_if_not(var_1_10 >= 16383);
 assume_abort_if_not(var_1_10 <= 32767);
 var_1_13 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_13 >= 127);
 assume_abort_if_not(var_1_13 <= 255);
 var_1_14 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_14 >= 1);
 assume_abort_if_not(var_1_14 <= 126);
 assume_abort_if_not(var_1_14 != 127);
 var_1_15 = __VERIFIER_nondet_short();
 assume_abort_if_not(var_1_15 >= 16383);
 assume_abort_if_not(var_1_15 <= 32766);
 var_1_18 = __VERIFIER_nondet_float();
 assume_abort_if_not((var_1_18 >= -922337.2036854765600e+13F && var_1_18 <= -1.0e-20F) || (var_1_18 <= 9223372.036854765600e+12F && var_1_18 >= 1.0e-20F ));
}
void updateLastVariables() {
 last_1_var_1_8 = var_1_8;
 last_1_var_1_11 = var_1_11;
}
int property() {
 return (((((last_1_var_1_11 != last_1_var_1_8) ? (var_1_1 == ((unsigned char) (var_1_4 + ((((((((var_1_5) < (var_1_6)) ? (var_1_5) : (var_1_6)))) > (var_1_7)) ? (((((var_1_5) < (var_1_6)) ? (var_1_5) : (var_1_6)))) : (var_1_7)))))) : (var_1_1 == ((unsigned char) var_1_4))) && (var_1_9 ? (var_1_8 == ((unsigned short int) ((var_1_10 + 23103) - (32 + var_1_6)))) : 1)) && ((var_1_1 < var_1_16) ? ((((- 8) / (var_1_13 - var_1_14)) >= var_1_6) ? (var_1_11 == ((signed short int) (var_1_16 - (var_1_15 - var_1_14)))) : 1) : 1)) && ((! (var_1_5 > var_1_10)) ? (var_1_16 == ((signed short int) (32 - 8))) : (var_1_16 == ((signed short int) (var_1_13 - var_1_4))))) && (var_1_17 == ((float) var_1_18))
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
