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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch6950_1loop.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
unsigned char var_1_1 = 4;
signed short int var_1_3 = 128;
signed short int var_1_4 = 10;
unsigned char var_1_5 = 200;
unsigned char var_1_6 = 0;
unsigned char var_1_7 = 0;
unsigned char var_1_8 = 64;
signed char var_1_9 = -128;
unsigned char var_1_10 = 0;
unsigned char var_1_11 = 0;
double var_1_12 = 32.75;
double var_1_13 = 255.6;
signed short int var_1_14 = 8;
unsigned long int var_1_15 = 256;
unsigned long int var_1_16 = 4031871391;
unsigned long int var_1_17 = 3083112228;
unsigned long int var_1_18 = 3058504136;
unsigned long int var_1_19 = 1902304375;
unsigned char var_1_20 = 1;
unsigned char var_1_22 = 0;
unsigned char var_1_23 = 1;
unsigned char last_1_var_1_1 = 4;
signed char last_1_var_1_9 = -128;
signed short int last_1_var_1_14 = 8;
void initially(void) {
}
void step(void) {
 signed long int stepLocal_5 = last_1_var_1_9;
 if (stepLocal_5 < last_1_var_1_1) {
  var_1_20 = ((! (var_1_11 && var_1_22)) && (var_1_10 || var_1_23));
 } else {
  var_1_20 = var_1_23;
 }
 if (var_1_20 || (var_1_6 <= var_1_8)) {
  var_1_14 = var_1_6;
 }
 signed long int stepLocal_0 = var_1_3 - var_1_4;
 if (last_1_var_1_14 >= stepLocal_0) {
  var_1_1 = ((var_1_5 - ((((var_1_6) < (var_1_7)) ? (var_1_6) : (var_1_7)))) - var_1_8);
 } else {
  var_1_1 = (32 + var_1_7);
 }
 unsigned char stepLocal_2 = var_1_20;
 signed long int stepLocal_1 = var_1_8 - var_1_5;
 if (stepLocal_1 >= var_1_1) {
  if (stepLocal_2 || var_1_20) {
   var_1_9 = var_1_6;
  } else {
   var_1_9 = var_1_7;
  }
 } else {
  var_1_9 = var_1_5;
 }
 unsigned char stepLocal_4 = var_1_7;
 unsigned char stepLocal_3 = var_1_20;
 if (stepLocal_4 > var_1_1) {
  if (((var_1_1 + var_1_9) == var_1_1) && stepLocal_3) {
   if (! var_1_20) {
    var_1_12 = var_1_13;
   } else {
    var_1_12 = var_1_13;
   }
  } else {
   var_1_12 = var_1_13;
  }
 } else {
  var_1_12 = var_1_13;
 }
 if (var_1_12 < var_1_13) {
  var_1_15 = (((((((((var_1_16) > (var_1_17)) ? (var_1_16) : (var_1_17)))) > (((((3407568261u) > (var_1_18)) ? (3407568261u) : (var_1_18))))) ? (((((var_1_16) > (var_1_17)) ? (var_1_16) : (var_1_17)))) : (((((3407568261u) > (var_1_18)) ? (3407568261u) : (var_1_18)))))) - (var_1_19 - 32u));
 } else {
  var_1_15 = (var_1_18 - var_1_19);
 }
}
void updateVariables() {
 var_1_3 = __VERIFIER_nondet_short();
 assume_abort_if_not(var_1_3 >= -1);
 assume_abort_if_not(var_1_3 <= 32767);
 var_1_4 = __VERIFIER_nondet_short();
 assume_abort_if_not(var_1_4 >= 0);
 assume_abort_if_not(var_1_4 <= 32767);
 var_1_5 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_5 >= 190);
 assume_abort_if_not(var_1_5 <= 254);
 var_1_6 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_6 >= 0);
 assume_abort_if_not(var_1_6 <= 63);
 var_1_7 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_7 >= 0);
 assume_abort_if_not(var_1_7 <= 63);
 var_1_8 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_8 >= 0);
 assume_abort_if_not(var_1_8 <= 127);
 var_1_10 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_10 >= 0);
 assume_abort_if_not(var_1_10 <= 1);
 var_1_11 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_11 >= 0);
 assume_abort_if_not(var_1_11 <= 1);
 var_1_13 = __VERIFIER_nondet_double();
 assume_abort_if_not((var_1_13 >= -922337.2036854765600e+13F && var_1_13 <= -1.0e-20F) || (var_1_13 <= 9223372.036854765600e+12F && var_1_13 >= 1.0e-20F ));
 var_1_16 = __VERIFIER_nondet_ulong();
 assume_abort_if_not(var_1_16 >= 2147483647);
 assume_abort_if_not(var_1_16 <= 4294967294);
 var_1_17 = __VERIFIER_nondet_ulong();
 assume_abort_if_not(var_1_17 >= 2147483647);
 assume_abort_if_not(var_1_17 <= 4294967294);
 var_1_18 = __VERIFIER_nondet_ulong();
 assume_abort_if_not(var_1_18 >= 2147483647);
 assume_abort_if_not(var_1_18 <= 4294967294);
 var_1_19 = __VERIFIER_nondet_ulong();
 assume_abort_if_not(var_1_19 >= 1073741823);
 assume_abort_if_not(var_1_19 <= 2147483647);
 var_1_22 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_22 >= 0);
 assume_abort_if_not(var_1_22 <= 0);
 var_1_23 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_23 >= 1);
 assume_abort_if_not(var_1_23 <= 1);
}
void updateLastVariables() {
 last_1_var_1_1 = var_1_1;
 last_1_var_1_9 = var_1_9;
 last_1_var_1_14 = var_1_14;
}
int property() {
 return ((((((last_1_var_1_14 >= (var_1_3 - var_1_4)) ? (var_1_1 == ((unsigned char) ((var_1_5 - ((((var_1_6) < (var_1_7)) ? (var_1_6) : (var_1_7)))) - var_1_8))) : (var_1_1 == ((unsigned char) (32 + var_1_7)))) && (((var_1_8 - var_1_5) >= var_1_1) ? ((var_1_20 || var_1_20) ? (var_1_9 == ((signed char) var_1_6)) : (var_1_9 == ((signed char) var_1_7))) : (var_1_9 == ((signed char) var_1_5)))) && ((var_1_7 > var_1_1) ? ((((var_1_1 + var_1_9) == var_1_1) && var_1_20) ? ((! var_1_20) ? (var_1_12 == ((double) var_1_13)) : (var_1_12 == ((double) var_1_13))) : (var_1_12 == ((double) var_1_13))) : (var_1_12 == ((double) var_1_13)))) && ((var_1_20 || (var_1_6 <= var_1_8)) ? (var_1_14 == ((signed short int) var_1_6)) : 1)) && ((var_1_12 < var_1_13) ? (var_1_15 == ((unsigned long int) (((((((((var_1_16) > (var_1_17)) ? (var_1_16) : (var_1_17)))) > (((((3407568261u) > (var_1_18)) ? (3407568261u) : (var_1_18))))) ? (((((var_1_16) > (var_1_17)) ? (var_1_16) : (var_1_17)))) : (((((3407568261u) > (var_1_18)) ? (3407568261u) : (var_1_18)))))) - (var_1_19 - 32u)))) : (var_1_15 == ((unsigned long int) (var_1_18 - var_1_19))))) && ((last_1_var_1_9 < last_1_var_1_1) ? (var_1_20 == ((unsigned char) ((! (var_1_11 && var_1_22)) && (var_1_10 || var_1_23)))) : (var_1_20 == ((unsigned char) var_1_23)))
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
