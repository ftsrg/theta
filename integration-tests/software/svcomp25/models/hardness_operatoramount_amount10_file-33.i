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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch33Amount10.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
float var_1_1 = 256.25;
float var_1_6 = 1000000000.625;
signed char var_1_7 = -128;
signed char var_1_8 = 32;
unsigned long int var_1_9 = 32;
unsigned char var_1_10 = 0;
void initially(void) {
}
void step(void) {
 var_1_7 = var_1_8;
 var_1_9 = var_1_7;
 var_1_10 = 1;
 unsigned long int stepLocal_1 = var_1_9;
 unsigned char stepLocal_0 = var_1_10 && var_1_10;
 if ((var_1_7 >= var_1_9) || stepLocal_0) {
  if (stepLocal_1 <= var_1_7) {
   var_1_1 = var_1_6;
  }
 }
}
void updateVariables() {
 var_1_6 = __VERIFIER_nondet_float();
 assume_abort_if_not((var_1_6 >= -922337.2036854765600e+13F && var_1_6 <= -1.0e-20F) || (var_1_6 <= 9223372.036854765600e+12F && var_1_6 >= 1.0e-20F ));
 var_1_8 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_8 >= -127);
 assume_abort_if_not(var_1_8 <= 126);
}
void updateLastVariables() {
}
int property() {
 return (((((var_1_7 >= var_1_9) || (var_1_10 && var_1_10)) ? ((var_1_9 <= var_1_7) ? (var_1_1 == ((float) var_1_6)) : 1) : 1) && (var_1_7 == ((signed char) var_1_8))) && (var_1_9 == ((unsigned long int) var_1_7))) && (var_1_10 == ((unsigned char) 1))
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
