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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch47has_floats.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
double var_1_1 = 24.575;
double var_1_8 = 3.5;
signed char var_1_9 = 16;
signed char var_1_10 = 16;
signed char var_1_11 = 4;
signed long int var_1_12 = 8;
unsigned char var_1_13 = 1;
unsigned char var_1_14 = 1;
double var_1_15 = 3.8;
signed long int last_1_var_1_12 = 8;
void initially(void) {
}
void step(void) {
 if (-4 > last_1_var_1_12) {
  if ((~ last_1_var_1_12) <= last_1_var_1_12) {
   var_1_9 = ((((var_1_10 + var_1_11) < 0 ) ? -(var_1_10 + var_1_11) : (var_1_10 + var_1_11)));
  }
 } else {
  var_1_9 = var_1_10;
 }
 unsigned char stepLocal_0 = ! var_1_13;
 if (stepLocal_0 || var_1_14) {
  if (! var_1_14) {
   var_1_12 = (((((((var_1_9) < (var_1_9)) ? (var_1_9) : (var_1_9))) < 0 ) ? -((((var_1_9) < (var_1_9)) ? (var_1_9) : (var_1_9))) : ((((var_1_9) < (var_1_9)) ? (var_1_9) : (var_1_9)))));
  } else {
   var_1_12 = var_1_9;
  }
 }
 var_1_15 = var_1_8;
 if (var_1_15 <= var_1_15) {
  if ((var_1_12 + var_1_12) >= (var_1_12 + var_1_9)) {
   var_1_1 = ((((var_1_8) < 0 ) ? -(var_1_8) : (var_1_8)));
  }
 } else {
  if (var_1_12 > var_1_9) {
   var_1_1 = var_1_8;
  }
 }
}
void updateVariables() {
 var_1_8 = __VERIFIER_nondet_double();
 assume_abort_if_not((var_1_8 >= -922337.2036854765600e+13F && var_1_8 <= -1.0e-20F) || (var_1_8 <= 9223372.036854765600e+12F && var_1_8 >= 1.0e-20F ));
 var_1_10 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_10 >= -63);
 assume_abort_if_not(var_1_10 <= 63);
 var_1_11 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_11 >= -63);
 assume_abort_if_not(var_1_11 <= 63);
 var_1_13 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_13 >= 0);
 assume_abort_if_not(var_1_13 <= 1);
 var_1_14 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_14 >= 0);
 assume_abort_if_not(var_1_14 <= 1);
}
void updateLastVariables() {
 last_1_var_1_12 = var_1_12;
}
int property() {
 return ((((var_1_15 <= var_1_15) ? (((var_1_12 + var_1_12) >= (var_1_12 + var_1_9)) ? (var_1_1 == ((double) ((((var_1_8) < 0 ) ? -(var_1_8) : (var_1_8))))) : 1) : ((var_1_12 > var_1_9) ? (var_1_1 == ((double) var_1_8)) : 1)) && ((-4 > last_1_var_1_12) ? (((~ last_1_var_1_12) <= last_1_var_1_12) ? (var_1_9 == ((signed char) ((((var_1_10 + var_1_11) < 0 ) ? -(var_1_10 + var_1_11) : (var_1_10 + var_1_11))))) : 1) : (var_1_9 == ((signed char) var_1_10)))) && (((! var_1_13) || var_1_14) ? ((! var_1_14) ? (var_1_12 == ((signed long int) (((((((var_1_9) < (var_1_9)) ? (var_1_9) : (var_1_9))) < 0 ) ? -((((var_1_9) < (var_1_9)) ? (var_1_9) : (var_1_9))) : ((((var_1_9) < (var_1_9)) ? (var_1_9) : (var_1_9))))))) : (var_1_12 == ((signed long int) var_1_9))) : 1)) && (var_1_15 == ((double) var_1_8))
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
