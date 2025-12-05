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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch4625_while.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
unsigned char var_1_1 = 1;
double var_1_2 = 31.75;
signed char var_1_4 = -8;
unsigned char var_1_6 = 0;
unsigned char var_1_7 = 1;
unsigned char var_1_8 = 16;
unsigned char var_1_9 = 8;
signed long int var_1_10 = 256;
signed long int last_1_var_1_10 = 256;
void initially(void) {
}
void step(void) {
 signed char stepLocal_3 = var_1_4;
 unsigned char stepLocal_2 = var_1_7;
 if (2 != stepLocal_3) {
  var_1_8 = var_1_9;
 } else {
  if ((var_1_9 <= last_1_var_1_10) && stepLocal_2) {
   var_1_8 = 128;
  } else {
   var_1_8 = var_1_9;
  }
 }
 signed long int stepLocal_1 = var_1_8 / var_1_4;
 signed long int stepLocal_0 = (((var_1_4) < (var_1_8)) ? (var_1_4) : (var_1_8));
 if ((- var_1_2) >= 16.75) {
  if (stepLocal_1 >= var_1_8) {
   if (stepLocal_0 > -32) {
    var_1_1 = 0;
   } else {
    var_1_1 = var_1_6;
   }
  } else {
   var_1_1 = var_1_7;
  }
 } else {
  var_1_1 = var_1_6;
 }
 signed long int stepLocal_4 = var_1_8 * var_1_8;
 if (0 > stepLocal_4) {
  if (var_1_1) {
   var_1_10 = 5;
  }
 }
}
void updateVariables() {
 var_1_2 = __VERIFIER_nondet_double();
 assume_abort_if_not((var_1_2 >= -922337.2036854776000e+13F && var_1_2 <= -1.0e-20F) || (var_1_2 <= 9223372.036854776000e+12F && var_1_2 >= 1.0e-20F ));
 var_1_4 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_4 >= -128);
 assume_abort_if_not(var_1_4 <= 127);
 assume_abort_if_not(var_1_4 != 0);
 var_1_6 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_6 >= 0);
 assume_abort_if_not(var_1_6 <= 0);
 var_1_7 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_7 >= 1);
 assume_abort_if_not(var_1_7 <= 1);
 var_1_9 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_9 >= 0);
 assume_abort_if_not(var_1_9 <= 254);
}
void updateLastVariables() {
 last_1_var_1_10 = var_1_10;
}
int property() {
 return ((((- var_1_2) >= 16.75) ? (((var_1_8 / var_1_4) >= var_1_8) ? ((((((var_1_4) < (var_1_8)) ? (var_1_4) : (var_1_8))) > -32) ? (var_1_1 == ((unsigned char) 0)) : (var_1_1 == ((unsigned char) var_1_6))) : (var_1_1 == ((unsigned char) var_1_7))) : (var_1_1 == ((unsigned char) var_1_6))) && ((2 != var_1_4) ? (var_1_8 == ((unsigned char) var_1_9)) : (((var_1_9 <= last_1_var_1_10) && var_1_7) ? (var_1_8 == ((unsigned char) 128)) : (var_1_8 == ((unsigned char) var_1_9))))) && ((0 > (var_1_8 * var_1_8)) ? (var_1_1 ? (var_1_10 == ((signed long int) 5)) : 1) : 1)
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
