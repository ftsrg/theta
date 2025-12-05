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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch37normal.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
unsigned char var_1_1 = 8;
unsigned short int var_1_2 = 59049;
unsigned short int var_1_3 = 100;
unsigned char var_1_6 = 16;
signed char var_1_7 = -25;
signed char var_1_8 = 16;
signed char var_1_9 = 25;
signed char var_1_10 = -10;
signed char var_1_11 = 0;
float var_1_12 = 25.1;
unsigned long int var_1_13 = 2531521428;
signed long int var_1_14 = -128;
signed long int var_1_15 = 256;
signed short int var_1_16 = -16;
void initially(void) {
}
void step(void) {
 var_1_14 = var_1_8;
 var_1_16 = var_1_14;
 signed long int stepLocal_0 = (((var_1_14) < 0 ) ? -(var_1_14) : (var_1_14));
 if (var_1_2 <= stepLocal_0) {
  var_1_7 = ((var_1_8 - (1 + var_1_9)) + var_1_10);
 } else {
  var_1_7 = var_1_10;
 }
 var_1_15 = var_1_16;
 if (((var_1_2 - var_1_3) ^ (var_1_15 * var_1_16)) <= -64) {
  var_1_1 = var_1_6;
 } else {
  var_1_1 = var_1_6;
 }
 unsigned char stepLocal_1 = var_1_1;
 if (2.75f > var_1_12) {
  var_1_11 = (var_1_10 + var_1_8);
 } else {
  if ((var_1_13 - ((((var_1_14) > (var_1_8)) ? (var_1_14) : (var_1_8)))) > stepLocal_1) {
   var_1_11 = ((((((((var_1_8) < ((1 + 5))) ? (var_1_8) : ((1 + 5))))) < (var_1_10)) ? (((((var_1_8) < ((1 + 5))) ? (var_1_8) : ((1 + 5))))) : (var_1_10)));
  }
 }
}
void updateVariables() {
 var_1_2 = __VERIFIER_nondet_ushort();
 assume_abort_if_not(var_1_2 >= 32767);
 assume_abort_if_not(var_1_2 <= 65535);
 var_1_3 = __VERIFIER_nondet_ushort();
 assume_abort_if_not(var_1_3 >= 0);
 assume_abort_if_not(var_1_3 <= 32767);
 var_1_6 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_6 >= 0);
 assume_abort_if_not(var_1_6 <= 254);
 var_1_8 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_8 >= 0);
 assume_abort_if_not(var_1_8 <= 63);
 var_1_9 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_9 >= 0);
 assume_abort_if_not(var_1_9 <= 31);
 var_1_10 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_10 >= -63);
 assume_abort_if_not(var_1_10 <= 63);
 var_1_12 = __VERIFIER_nondet_float();
 assume_abort_if_not((var_1_12 >= -922337.2036854776000e+13F && var_1_12 <= -1.0e-20F) || (var_1_12 <= 9223372.036854776000e+12F && var_1_12 >= 1.0e-20F ));
 var_1_13 = __VERIFIER_nondet_ulong();
 assume_abort_if_not(var_1_13 >= 2147483647);
 assume_abort_if_not(var_1_13 <= 4294967295);
}
void updateLastVariables() {
}
int property() {
 return ((((((((var_1_2 - var_1_3) ^ (var_1_15 * var_1_16)) <= -64) ? (var_1_1 == ((unsigned char) var_1_6)) : (var_1_1 == ((unsigned char) var_1_6))) && ((var_1_2 <= ((((var_1_14) < 0 ) ? -(var_1_14) : (var_1_14)))) ? (var_1_7 == ((signed char) ((var_1_8 - (1 + var_1_9)) + var_1_10))) : (var_1_7 == ((signed char) var_1_10)))) && ((2.75f > var_1_12) ? (var_1_11 == ((signed char) (var_1_10 + var_1_8))) : (((var_1_13 - ((((var_1_14) > (var_1_8)) ? (var_1_14) : (var_1_8)))) > var_1_1) ? (var_1_11 == ((signed char) ((((((((var_1_8) < ((1 + 5))) ? (var_1_8) : ((1 + 5))))) < (var_1_10)) ? (((((var_1_8) < ((1 + 5))) ? (var_1_8) : ((1 + 5))))) : (var_1_10))))) : 1))) && (var_1_14 == ((signed long int) var_1_8))) && (var_1_15 == ((signed long int) var_1_16))) && (var_1_16 == ((signed short int) var_1_14))
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
