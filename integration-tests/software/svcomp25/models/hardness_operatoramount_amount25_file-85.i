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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch85Amount25.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
signed long int var_1_1 = 16;
unsigned char var_1_2 = 0;
signed long int var_1_3 = -64;
signed long int var_1_4 = -4;
unsigned char var_1_5 = 1;
unsigned char var_1_6 = 0;
signed char var_1_7 = 32;
signed char var_1_8 = -8;
signed char var_1_9 = 10;
double var_1_10 = 1.6;
double var_1_11 = 127.25;
double var_1_12 = 2.5;
void initially(void) {
}
void step(void) {
 signed long int stepLocal_0 = var_1_3;
 if (var_1_6) {
  if (stepLocal_0 <= var_1_4) {
   var_1_7 = ((((var_1_8) > (var_1_9)) ? (var_1_8) : (var_1_9)));
  }
 }
 if (var_1_2) {
  var_1_1 = (((((var_1_7 + var_1_7)) < (-16)) ? ((var_1_7 + var_1_7)) : (-16)));
 } else {
  if (var_1_5) {
   var_1_1 = (var_1_7 + -4);
  } else {
   if (var_1_6) {
    var_1_1 = var_1_7;
   } else {
    var_1_1 = var_1_7;
   }
  }
 }
 unsigned char stepLocal_2 = var_1_5;
 signed char stepLocal_1 = var_1_9;
 if (! var_1_6) {
  var_1_10 = ((((var_1_11) < (var_1_12)) ? (var_1_11) : (var_1_12)));
 } else {
  if ((var_1_7 | var_1_1) <= stepLocal_1) {
   if (stepLocal_2 && var_1_6) {
    var_1_10 = var_1_12;
   } else {
    var_1_10 = 5.5;
   }
  }
 }
}
void updateVariables() {
 var_1_2 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_2 >= 0);
 assume_abort_if_not(var_1_2 <= 1);
 var_1_3 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_3 >= -1073741823);
 assume_abort_if_not(var_1_3 <= 1073741823);
 var_1_4 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_4 >= -1073741823);
 assume_abort_if_not(var_1_4 <= 1073741823);
 var_1_5 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_5 >= 0);
 assume_abort_if_not(var_1_5 <= 1);
 var_1_6 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_6 >= 0);
 assume_abort_if_not(var_1_6 <= 1);
 var_1_8 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_8 >= -127);
 assume_abort_if_not(var_1_8 <= 126);
 var_1_9 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_9 >= -127);
 assume_abort_if_not(var_1_9 <= 126);
 var_1_11 = __VERIFIER_nondet_double();
 assume_abort_if_not((var_1_11 >= -922337.2036854765600e+13F && var_1_11 <= -1.0e-20F) || (var_1_11 <= 9223372.036854765600e+12F && var_1_11 >= 1.0e-20F ));
 var_1_12 = __VERIFIER_nondet_double();
 assume_abort_if_not((var_1_12 >= -922337.2036854765600e+13F && var_1_12 <= -1.0e-20F) || (var_1_12 <= 9223372.036854765600e+12F && var_1_12 >= 1.0e-20F ));
}
void updateLastVariables() {
}
int property() {
 return ((var_1_2 ? (var_1_1 == ((signed long int) (((((var_1_7 + var_1_7)) < (-16)) ? ((var_1_7 + var_1_7)) : (-16))))) : (var_1_5 ? (var_1_1 == ((signed long int) (var_1_7 + -4))) : (var_1_6 ? (var_1_1 == ((signed long int) var_1_7)) : (var_1_1 == ((signed long int) var_1_7))))) && (var_1_6 ? ((var_1_3 <= var_1_4) ? (var_1_7 == ((signed char) ((((var_1_8) > (var_1_9)) ? (var_1_8) : (var_1_9))))) : 1) : 1)) && ((! var_1_6) ? (var_1_10 == ((double) ((((var_1_11) < (var_1_12)) ? (var_1_11) : (var_1_12))))) : (((var_1_7 | var_1_1) <= var_1_9) ? ((var_1_5 && var_1_6) ? (var_1_10 == ((double) var_1_12)) : (var_1_10 == ((double) 5.5))) : 1))
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
