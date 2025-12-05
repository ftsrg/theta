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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch36normal.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
unsigned long int var_1_1 = 1;
float var_1_3 = 9999999999.875;
unsigned char var_1_4 = 0;
float var_1_5 = 4.25;
unsigned char var_1_7 = 1;
unsigned char var_1_9 = 1;
double var_1_10 = 64.2;
double var_1_11 = 9.5;
double var_1_12 = 199.5;
double var_1_13 = 3.5;
unsigned char var_1_14 = 1;
unsigned char var_1_16 = 2;
unsigned char last_1_var_1_14 = 1;
void initially(void) {
}
void step(void) {
 if ((last_1_var_1_14 >> last_1_var_1_14) < (- last_1_var_1_14)) {
  var_1_7 = (var_1_4 || var_1_9);
 }
 if (var_1_13 == (- var_1_12)) {
  if (var_1_7 && var_1_7) {
   var_1_14 = var_1_16;
  } else {
   var_1_14 = var_1_16;
  }
 } else {
  var_1_14 = 0;
 }
 if (var_1_5 > var_1_3) {
  var_1_10 = 4.6;
 } else {
  var_1_10 = ((((var_1_11) > (((((var_1_12) > (var_1_13)) ? (var_1_12) : (var_1_13))))) ? (var_1_11) : (((((var_1_12) > (var_1_13)) ? (var_1_12) : (var_1_13))))));
 }
 unsigned char stepLocal_0 = var_1_10 > var_1_10;
 if (stepLocal_0 && var_1_7) {
  if (((((var_1_10) > ((- var_1_10))) ? (var_1_10) : ((- var_1_10)))) != var_1_10) {
   if (var_1_7) {
    var_1_1 = 10u;
   } else {
    var_1_1 = var_1_14;
   }
  } else {
   var_1_1 = var_1_14;
  }
 } else {
  var_1_1 = var_1_14;
 }
}
void updateVariables() {
 var_1_3 = __VERIFIER_nondet_float();
 assume_abort_if_not((var_1_3 >= -922337.2036854776000e+13F && var_1_3 <= -1.0e-20F) || (var_1_3 <= 9223372.036854776000e+12F && var_1_3 >= 1.0e-20F ));
 var_1_4 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_4 >= 0);
 assume_abort_if_not(var_1_4 <= 1);
 var_1_5 = __VERIFIER_nondet_float();
 assume_abort_if_not((var_1_5 >= -922337.2036854776000e+13F && var_1_5 <= -1.0e-20F) || (var_1_5 <= 9223372.036854776000e+12F && var_1_5 >= 1.0e-20F ));
 var_1_9 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_9 >= 1);
 assume_abort_if_not(var_1_9 <= 1);
 var_1_11 = __VERIFIER_nondet_double();
 assume_abort_if_not((var_1_11 >= -922337.2036854765600e+13F && var_1_11 <= -1.0e-20F) || (var_1_11 <= 9223372.036854765600e+12F && var_1_11 >= 1.0e-20F ));
 var_1_12 = __VERIFIER_nondet_double();
 assume_abort_if_not((var_1_12 >= -922337.2036854765600e+13F && var_1_12 <= -1.0e-20F) || (var_1_12 <= 9223372.036854765600e+12F && var_1_12 >= 1.0e-20F ));
 var_1_13 = __VERIFIER_nondet_double();
 assume_abort_if_not((var_1_13 >= -922337.2036854765600e+13F && var_1_13 <= -1.0e-20F) || (var_1_13 <= 9223372.036854765600e+12F && var_1_13 >= 1.0e-20F ));
 var_1_16 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_16 >= 0);
 assume_abort_if_not(var_1_16 <= 254);
}
void updateLastVariables() {
 last_1_var_1_14 = var_1_14;
}
int property() {
 return (((((var_1_10 > var_1_10) && var_1_7) ? ((((((var_1_10) > ((- var_1_10))) ? (var_1_10) : ((- var_1_10)))) != var_1_10) ? (var_1_7 ? (var_1_1 == ((unsigned long int) 10u)) : (var_1_1 == ((unsigned long int) var_1_14))) : (var_1_1 == ((unsigned long int) var_1_14))) : (var_1_1 == ((unsigned long int) var_1_14))) && (((last_1_var_1_14 >> last_1_var_1_14) < (- last_1_var_1_14)) ? (var_1_7 == ((unsigned char) (var_1_4 || var_1_9))) : 1)) && ((var_1_5 > var_1_3) ? (var_1_10 == ((double) 4.6)) : (var_1_10 == ((double) ((((var_1_11) > (((((var_1_12) > (var_1_13)) ? (var_1_12) : (var_1_13))))) ? (var_1_11) : (((((var_1_12) > (var_1_13)) ? (var_1_12) : (var_1_13)))))))))) && ((var_1_13 == (- var_1_12)) ? ((var_1_7 && var_1_7) ? (var_1_14 == ((unsigned char) var_1_16)) : (var_1_14 == ((unsigned char) var_1_16))) : (var_1_14 == ((unsigned char) 0)))
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
