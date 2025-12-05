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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch54Amount25.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
unsigned char var_1_1 = 16;
unsigned char var_1_3 = 10;
unsigned char var_1_4 = 0;
unsigned char var_1_6 = 1;
unsigned char var_1_7 = 0;
unsigned char var_1_8 = 0;
unsigned long int var_1_9 = 5;
unsigned long int var_1_10 = 3126062476;
unsigned short int var_1_13 = 10;
signed long int var_1_14 = 128;
float var_1_15 = 4.2;
float var_1_16 = 5.1;
void initially(void) {
}
void step(void) {
 var_1_13 = var_1_3;
 var_1_14 = var_1_3;
 var_1_15 = var_1_16;
 unsigned short int stepLocal_0 = var_1_13;
 if (-4 >= stepLocal_0) {
  var_1_1 = ((((var_1_3) < (((((1) < 0 ) ? -(1) : (1))))) ? (var_1_3) : (((((1) < 0 ) ? -(1) : (1))))));
 }
 signed long int stepLocal_2 = var_1_14;
 if (var_1_3 < stepLocal_2) {
  var_1_9 = (((((3851651024u - var_1_3)) < ((((((var_1_10 - var_1_13)) > ((var_1_1 + var_1_1))) ? ((var_1_10 - var_1_13)) : ((var_1_1 + var_1_1)))))) ? ((3851651024u - var_1_3)) : ((((((var_1_10 - var_1_13)) > ((var_1_1 + var_1_1))) ? ((var_1_10 - var_1_13)) : ((var_1_1 + var_1_1)))))));
 }
 unsigned long int stepLocal_1 = 8 * var_1_9;
 if (stepLocal_1 == ((((10) > (var_1_9)) ? (10) : (var_1_9)))) {
  if (var_1_6) {
   var_1_4 = (var_1_7 && var_1_8);
  } else {
   var_1_4 = var_1_8;
  }
 } else {
  var_1_4 = var_1_8;
 }
}
void updateVariables() {
 var_1_3 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_3 >= 0);
 assume_abort_if_not(var_1_3 <= 254);
 var_1_6 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_6 >= 0);
 assume_abort_if_not(var_1_6 <= 1);
 var_1_7 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_7 >= 0);
 assume_abort_if_not(var_1_7 <= 1);
 var_1_8 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_8 >= 0);
 assume_abort_if_not(var_1_8 <= 0);
 var_1_10 = __VERIFIER_nondet_ulong();
 assume_abort_if_not(var_1_10 >= 2147483647);
 assume_abort_if_not(var_1_10 <= 4294967294);
 var_1_16 = __VERIFIER_nondet_float();
 assume_abort_if_not((var_1_16 >= -922337.2036854765600e+13F && var_1_16 <= -1.0e-20F) || (var_1_16 <= 9223372.036854765600e+12F && var_1_16 >= 1.0e-20F ));
}
void updateLastVariables() {
}
int property() {
 return ((((((-4 >= var_1_13) ? (var_1_1 == ((unsigned char) ((((var_1_3) < (((((1) < 0 ) ? -(1) : (1))))) ? (var_1_3) : (((((1) < 0 ) ? -(1) : (1)))))))) : 1) && (((8 * var_1_9) == ((((10) > (var_1_9)) ? (10) : (var_1_9)))) ? (var_1_6 ? (var_1_4 == ((unsigned char) (var_1_7 && var_1_8))) : (var_1_4 == ((unsigned char) var_1_8))) : (var_1_4 == ((unsigned char) var_1_8)))) && ((var_1_3 < var_1_14) ? (var_1_9 == ((unsigned long int) (((((3851651024u - var_1_3)) < ((((((var_1_10 - var_1_13)) > ((var_1_1 + var_1_1))) ? ((var_1_10 - var_1_13)) : ((var_1_1 + var_1_1)))))) ? ((3851651024u - var_1_3)) : ((((((var_1_10 - var_1_13)) > ((var_1_1 + var_1_1))) ? ((var_1_10 - var_1_13)) : ((var_1_1 + var_1_1))))))))) : 1)) && (var_1_13 == ((unsigned short int) var_1_3))) && (var_1_14 == ((signed long int) var_1_3))) && (var_1_15 == ((float) var_1_16))
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
