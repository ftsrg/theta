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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch3125_1loop.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
signed long int var_1_1 = 200;
unsigned char var_1_2 = 0;
signed long int var_1_3 = 1107940323;
unsigned char var_1_6 = 0;
unsigned char var_1_7 = 0;
unsigned char var_1_8 = 16;
unsigned char var_1_9 = 16;
unsigned short int var_1_10 = 4;
double var_1_11 = 1000000.5;
double var_1_12 = 1.25;
signed long int last_1_var_1_1 = 200;
unsigned char last_1_var_1_8 = 16;
unsigned short int last_1_var_1_10 = 4;
void initially(void) {
}
void step(void) {
 signed long int stepLocal_2 = last_1_var_1_8;
 signed long int stepLocal_1 = var_1_3 * last_1_var_1_8;
 if (stepLocal_1 >= last_1_var_1_1) {
  var_1_10 = (2 + var_1_9);
 } else {
  if (stepLocal_2 == (last_1_var_1_8 ^ last_1_var_1_1)) {
   var_1_10 = (var_1_9 + ((((last_1_var_1_1) < (4)) ? (last_1_var_1_1) : (4))));
  } else {
   var_1_10 = last_1_var_1_1;
  }
 }
 signed long int stepLocal_0 = last_1_var_1_10 / var_1_3;
 if (stepLocal_0 >= (500 - last_1_var_1_10)) {
  var_1_8 = var_1_9;
 }
 if (var_1_2) {
  var_1_1 = ((var_1_3 - var_1_10) - var_1_8);
 } else {
  if (var_1_6 && var_1_7) {
   var_1_1 = var_1_10;
  }
 }
 var_1_11 = var_1_12;
}
void updateVariables() {
 var_1_2 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_2 >= 0);
 assume_abort_if_not(var_1_2 <= 1);
 var_1_3 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_3 >= 1073741822);
 assume_abort_if_not(var_1_3 <= 2147483646);
 var_1_6 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_6 >= 0);
 assume_abort_if_not(var_1_6 <= 1);
 var_1_7 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_7 >= 0);
 assume_abort_if_not(var_1_7 <= 1);
 var_1_9 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_9 >= 0);
 assume_abort_if_not(var_1_9 <= 254);
 var_1_12 = __VERIFIER_nondet_double();
 assume_abort_if_not((var_1_12 >= -922337.2036854765600e+13F && var_1_12 <= -1.0e-20F) || (var_1_12 <= 9223372.036854765600e+12F && var_1_12 >= 1.0e-20F ));
}
void updateLastVariables() {
 last_1_var_1_1 = var_1_1;
 last_1_var_1_8 = var_1_8;
 last_1_var_1_10 = var_1_10;
}
int property() {
 return (((var_1_2 ? (var_1_1 == ((signed long int) ((var_1_3 - var_1_10) - var_1_8))) : ((var_1_6 && var_1_7) ? (var_1_1 == ((signed long int) var_1_10)) : 1)) && (((last_1_var_1_10 / var_1_3) >= (500 - last_1_var_1_10)) ? (var_1_8 == ((unsigned char) var_1_9)) : 1)) && (((var_1_3 * last_1_var_1_8) >= last_1_var_1_1) ? (var_1_10 == ((unsigned short int) (2 + var_1_9))) : ((last_1_var_1_8 == (last_1_var_1_8 ^ last_1_var_1_1)) ? (var_1_10 == ((unsigned short int) (var_1_9 + ((((last_1_var_1_1) < (4)) ? (last_1_var_1_1) : (4)))))) : (var_1_10 == ((unsigned short int) last_1_var_1_1))))) && (var_1_11 == ((double) var_1_12))
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
