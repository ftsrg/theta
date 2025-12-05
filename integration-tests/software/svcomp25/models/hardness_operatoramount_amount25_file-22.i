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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch22Amount25.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
signed short int var_1_1 = -5;
unsigned char var_1_4 = 0;
unsigned short int var_1_5 = 256;
unsigned short int var_1_6 = 44772;
float var_1_7 = 5.9;
float var_1_8 = 7.6;
float var_1_9 = 64.2;
float var_1_10 = 128.75;
unsigned long int var_1_11 = 8;
unsigned short int last_1_var_1_5 = 256;
unsigned long int last_1_var_1_11 = 8;
void initially(void) {
}
void step(void) {
 if (last_1_var_1_11 == last_1_var_1_5) {
  var_1_1 = (last_1_var_1_11 + -16);
 } else {
  if (var_1_4) {
   var_1_1 = last_1_var_1_5;
  }
 }
 signed short int stepLocal_0 = var_1_1;
 if (var_1_4) {
  var_1_5 = var_1_1;
 } else {
  if (stepLocal_0 <= var_1_1) {
   var_1_5 = ((((last_1_var_1_5) > ((var_1_6 - 8))) ? (last_1_var_1_5) : ((var_1_6 - 8))));
  }
 }
 unsigned short int stepLocal_1 = var_1_5;
 if (stepLocal_1 >= (var_1_1 & var_1_1)) {
  var_1_11 = ((((((((var_1_1) < (var_1_1)) ? (var_1_1) : (var_1_1)))) < (var_1_5)) ? (((((var_1_1) < (var_1_1)) ? (var_1_1) : (var_1_1)))) : (var_1_5)));
 } else {
  var_1_11 = var_1_1;
 }
 if (var_1_11 < var_1_11) {
  var_1_7 = (((10.25f + var_1_8) + var_1_9) + var_1_10);
 }
}
void updateVariables() {
 var_1_4 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_4 >= 0);
 assume_abort_if_not(var_1_4 <= 1);
 var_1_6 = __VERIFIER_nondet_ushort();
 assume_abort_if_not(var_1_6 >= 32767);
 assume_abort_if_not(var_1_6 <= 65534);
 var_1_8 = __VERIFIER_nondet_float();
 assume_abort_if_not((var_1_8 >= -115292.1504606845700e+13F && var_1_8 <= -1.0e-20F) || (var_1_8 <= 1152921.504606845700e+12F && var_1_8 >= 1.0e-20F ));
 var_1_9 = __VERIFIER_nondet_float();
 assume_abort_if_not((var_1_9 >= -230584.3009213691390e+13F && var_1_9 <= -1.0e-20F) || (var_1_9 <= 2305843.009213691390e+12F && var_1_9 >= 1.0e-20F ));
 var_1_10 = __VERIFIER_nondet_float();
 assume_abort_if_not((var_1_10 >= -461168.6018427382800e+13F && var_1_10 <= -1.0e-20F) || (var_1_10 <= 4611686.018427382800e+12F && var_1_10 >= 1.0e-20F ));
}
void updateLastVariables() {
 last_1_var_1_5 = var_1_5;
 last_1_var_1_11 = var_1_11;
}
int property() {
 return ((((last_1_var_1_11 == last_1_var_1_5) ? (var_1_1 == ((signed short int) (last_1_var_1_11 + -16))) : (var_1_4 ? (var_1_1 == ((signed short int) last_1_var_1_5)) : 1)) && (var_1_4 ? (var_1_5 == ((unsigned short int) var_1_1)) : ((var_1_1 <= var_1_1) ? (var_1_5 == ((unsigned short int) ((((last_1_var_1_5) > ((var_1_6 - 8))) ? (last_1_var_1_5) : ((var_1_6 - 8)))))) : 1))) && ((var_1_11 < var_1_11) ? (var_1_7 == ((float) (((10.25f + var_1_8) + var_1_9) + var_1_10))) : 1)) && ((var_1_5 >= (var_1_1 & var_1_1)) ? (var_1_11 == ((unsigned long int) ((((((((var_1_1) < (var_1_1)) ? (var_1_1) : (var_1_1)))) < (var_1_5)) ? (((((var_1_1) < (var_1_1)) ? (var_1_1) : (var_1_1)))) : (var_1_5))))) : (var_1_11 == ((unsigned long int) var_1_1)))
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
