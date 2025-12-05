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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch3925_1loop.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
signed short int var_1_1 = -5;
signed short int var_1_3 = 1000;
signed long int var_1_6 = 5;
float var_1_7 = 1.1;
float var_1_8 = 7.8;
float var_1_9 = 1.75;
unsigned char var_1_10 = 0;
signed char var_1_11 = 32;
unsigned char var_1_12 = 0;
unsigned char var_1_13 = 0;
unsigned char var_1_14 = 10;
unsigned char var_1_16 = 5;
signed long int last_1_var_1_6 = 5;
unsigned char last_1_var_1_10 = 0;
void initially(void) {
}
void step(void) {
 signed long int stepLocal_1 = last_1_var_1_6;
 if (last_1_var_1_10) {
  if (var_1_3 >= stepLocal_1) {
   var_1_14 = var_1_16;
  }
 }
 var_1_1 = ((((((16) > (4)) ? (16) : (4))) + var_1_14) - (var_1_14 + ((((var_1_14) < (var_1_14)) ? (var_1_14) : (var_1_14)))));
 if (var_1_14 >= var_1_1) {
  if (((((var_1_7 + var_1_8) < 0 ) ? -(var_1_7 + var_1_8) : (var_1_7 + var_1_8))) < var_1_9) {
   var_1_6 = ((((var_1_14) > (var_1_14)) ? (var_1_14) : (var_1_14)));
  } else {
   var_1_6 = var_1_14;
  }
 } else {
  var_1_6 = var_1_14;
 }
 signed long int stepLocal_0 = (((var_1_11) < 0 ) ? -(var_1_11) : (var_1_11));
 if (stepLocal_0 == var_1_14) {
  var_1_10 = (var_1_12 || var_1_13);
 }
}
void updateVariables() {
 var_1_3 = __VERIFIER_nondet_short();
 assume_abort_if_not(var_1_3 >= 0);
 assume_abort_if_not(var_1_3 <= 16383);
 var_1_7 = __VERIFIER_nondet_float();
 assume_abort_if_not((var_1_7 >= -922337.2036854776000e+13F && var_1_7 <= -1.0e-20F) || (var_1_7 <= 9223372.036854776000e+12F && var_1_7 >= 1.0e-20F ));
 var_1_8 = __VERIFIER_nondet_float();
 assume_abort_if_not((var_1_8 >= -922337.2036854776000e+13F && var_1_8 <= -1.0e-20F) || (var_1_8 <= 9223372.036854776000e+12F && var_1_8 >= 1.0e-20F ));
 var_1_9 = __VERIFIER_nondet_float();
 assume_abort_if_not((var_1_9 >= -922337.2036854776000e+13F && var_1_9 <= -1.0e-20F) || (var_1_9 <= 9223372.036854776000e+12F && var_1_9 >= 1.0e-20F ));
 var_1_11 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_11 >= -127);
 assume_abort_if_not(var_1_11 <= 127);
 var_1_12 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_12 >= 0);
 assume_abort_if_not(var_1_12 <= 1);
 var_1_13 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_13 >= 1);
 assume_abort_if_not(var_1_13 <= 1);
 var_1_16 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_16 >= 0);
 assume_abort_if_not(var_1_16 <= 254);
}
void updateLastVariables() {
 last_1_var_1_6 = var_1_6;
 last_1_var_1_10 = var_1_10;
}
int property() {
 return (((var_1_1 == ((signed short int) ((((((16) > (4)) ? (16) : (4))) + var_1_14) - (var_1_14 + ((((var_1_14) < (var_1_14)) ? (var_1_14) : (var_1_14))))))) && ((var_1_14 >= var_1_1) ? ((((((var_1_7 + var_1_8) < 0 ) ? -(var_1_7 + var_1_8) : (var_1_7 + var_1_8))) < var_1_9) ? (var_1_6 == ((signed long int) ((((var_1_14) > (var_1_14)) ? (var_1_14) : (var_1_14))))) : (var_1_6 == ((signed long int) var_1_14))) : (var_1_6 == ((signed long int) var_1_14)))) && ((((((var_1_11) < 0 ) ? -(var_1_11) : (var_1_11))) == var_1_14) ? (var_1_10 == ((unsigned char) (var_1_12 || var_1_13))) : 1)) && (last_1_var_1_10 ? ((var_1_3 >= last_1_var_1_6) ? (var_1_14 == ((unsigned char) var_1_16)) : 1) : 1)
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
