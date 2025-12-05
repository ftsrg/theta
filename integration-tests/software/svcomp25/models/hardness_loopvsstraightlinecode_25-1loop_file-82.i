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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch8225_1loop.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
float var_1_1 = 128.75;
unsigned char var_1_2 = 1;
float var_1_3 = 63.5;
float var_1_4 = 255.5;
unsigned char var_1_5 = 32;
unsigned char var_1_9 = 25;
signed long int var_1_10 = -10;
signed long int last_1_var_1_10 = -10;
void initially(void) {
}
void step(void) {
 signed long int stepLocal_0 = last_1_var_1_10 / -2;
 if (stepLocal_0 >= (last_1_var_1_10 | last_1_var_1_10)) {
  var_1_5 = ((((var_1_9) < 0 ) ? -(var_1_9) : (var_1_9)));
 } else {
  var_1_5 = var_1_9;
 }
 if (! var_1_2) {
  if (var_1_2) {
   var_1_1 = ((((var_1_3) > (var_1_4)) ? (var_1_3) : (var_1_4)));
  }
 }
 unsigned char stepLocal_1 = var_1_5;
 if (stepLocal_1 != var_1_5) {
  if (var_1_1 >= var_1_4) {
   var_1_10 = (((var_1_9 + var_1_5) + ((((var_1_5) < 0 ) ? -(var_1_5) : (var_1_5)))) - var_1_5);
  } else {
   if (var_1_2) {
    var_1_10 = var_1_5;
   } else {
    var_1_10 = var_1_5;
   }
  }
 } else {
  var_1_10 = var_1_9;
 }
}
void updateVariables() {
 var_1_2 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_2 >= 0);
 assume_abort_if_not(var_1_2 <= 1);
 var_1_3 = __VERIFIER_nondet_float();
 assume_abort_if_not((var_1_3 >= -922337.2036854765600e+13F && var_1_3 <= -1.0e-20F) || (var_1_3 <= 9223372.036854765600e+12F && var_1_3 >= 1.0e-20F ));
 var_1_4 = __VERIFIER_nondet_float();
 assume_abort_if_not((var_1_4 >= -922337.2036854765600e+13F && var_1_4 <= -1.0e-20F) || (var_1_4 <= 9223372.036854765600e+12F && var_1_4 >= 1.0e-20F ));
 var_1_9 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_9 >= 0);
 assume_abort_if_not(var_1_9 <= 254);
}
void updateLastVariables() {
 last_1_var_1_10 = var_1_10;
}
int property() {
 return (((! var_1_2) ? (var_1_2 ? (var_1_1 == ((float) ((((var_1_3) > (var_1_4)) ? (var_1_3) : (var_1_4))))) : 1) : 1) && (((last_1_var_1_10 / -2) >= (last_1_var_1_10 | last_1_var_1_10)) ? (var_1_5 == ((unsigned char) ((((var_1_9) < 0 ) ? -(var_1_9) : (var_1_9))))) : (var_1_5 == ((unsigned char) var_1_9)))) && ((var_1_5 != var_1_5) ? ((var_1_1 >= var_1_4) ? (var_1_10 == ((signed long int) (((var_1_9 + var_1_5) + ((((var_1_5) < 0 ) ? -(var_1_5) : (var_1_5)))) - var_1_5))) : (var_1_2 ? (var_1_10 == ((signed long int) var_1_5)) : (var_1_10 == ((signed long int) var_1_5)))) : (var_1_10 == ((signed long int) var_1_9)))
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
