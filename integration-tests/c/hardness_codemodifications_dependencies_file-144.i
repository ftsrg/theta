// This file is part of the SV-Benchmarks collection of verification tasks:
// https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks
//
// SPDX-FileCopyrightText: 2025 Jana Berger
//
// SPDX-License-Identifier: GPL-3.0-or-later

extern unsigned long __VERIFIER_nondet_ulong(void);
extern long __VERIFIER_nondet_long(void);
extern unsigned char __VERIFIER_nondet_uchar(void);
extern char __VERIFIER_nondet_char(void);
extern unsigned short __VERIFIER_nondet_ushort(void);
extern short __VERIFIER_nondet_short(void);
extern float __VERIFIER_nondet_float(void);
extern double __VERIFIER_nondet_double(void);
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error(void) { __assert_fail("0", "Req1_Prop1_Batch144dependencies.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
void initially(void);
void step(void);
void updateVariables(void);
void updateLastVariables(void);
int property(void);
int main(void);
unsigned char isInitial = 0;
signed long int var_1_1 = -8;
unsigned short int var_1_2 = 1000;
unsigned short int var_1_3 = 1;
unsigned short int var_1_4 = 0;
unsigned char var_1_5 = 1;
signed short int var_1_7 = -64;
signed short int var_1_8 = 200;
signed short int var_1_9 = 200;
signed short int var_1_10 = 8;
signed short int var_1_11 = -1;
double var_1_12 = 128.25;
double var_1_13 = 255.7;
double var_1_14 = 999999999999.375;
unsigned char var_1_15 = 1;
unsigned char var_1_17 = 1;
unsigned char var_1_18 = 1;
float var_1_19 = 63.6;
signed char var_1_20 = 16;
float var_1_21 = 1.375;
unsigned long int var_1_22 = 10;
signed char var_1_23 = 32;
signed char var_1_24 = 2;
signed char var_1_25 = 32;
unsigned char var_1_26 = 0;
unsigned char var_1_27 = 0;
unsigned char var_1_28 = 200;
unsigned long int last_1_var_1_22 = 10;
void initially(void) {
}
void step(void) {
 if (var_1_8 >= last_1_var_1_22) {
  var_1_15 = (var_1_17 && var_1_18);
 }
 var_1_7 = ((((var_1_8) < (((var_1_9 - var_1_10) + var_1_11))) ? (var_1_8) : (((var_1_9 - var_1_10) + var_1_11))));
 var_1_26 = (var_1_17 && var_1_27);
 if (var_1_2 == (var_1_3 ^ var_1_4)) {
  if (var_1_15 && var_1_26) {
   var_1_1 = var_1_2;
  } else {
   var_1_1 = (((((var_1_2 + var_1_3)) < (var_1_4)) ? ((var_1_2 + var_1_3)) : (var_1_4)));
  }
 }
 if (var_1_18 || (var_1_5 && var_1_15)) {
  var_1_22 = var_1_1;
 }
 if (((var_1_22 * var_1_9) <= var_1_1) || var_1_15) {
  var_1_12 = (var_1_13 + var_1_14);
 }
 if ((var_1_22 / var_1_20) <= var_1_22) {
  if (var_1_26) {
   var_1_19 = ((var_1_21 + ((((var_1_13) < 0 ) ? -(var_1_13) : (var_1_13)))) - (((((((1000000.625f) < 0 ) ? -(1000000.625f) : (1000000.625f))) < 0 ) ? -((((1000000.625f) < 0 ) ? -(1000000.625f) : (1000000.625f))) : ((((1000000.625f) < 0 ) ? -(1000000.625f) : (1000000.625f))))));
  } else {
   var_1_19 = var_1_13;
  }
 }
 if (var_1_17 && var_1_26) {
  var_1_23 = (var_1_24 - var_1_25);
 }
 if (var_1_21 < var_1_12) {
  if (var_1_11 >= ((((var_1_4) < (var_1_7)) ? (var_1_4) : (var_1_7)))) {
   if (var_1_17) {
    var_1_28 = var_1_25;
   } else {
    var_1_28 = 32;
   }
  }
 } else {
  var_1_28 = var_1_25;
 }
}
void updateVariables(void) {
 var_1_2 = __VERIFIER_nondet_ushort();
 assume_abort_if_not(var_1_2 >= 0);
 assume_abort_if_not(var_1_2 <= 65535);
 var_1_3 = __VERIFIER_nondet_ushort();
 assume_abort_if_not(var_1_3 >= 0);
 assume_abort_if_not(var_1_3 <= 65535);
 var_1_4 = __VERIFIER_nondet_ushort();
 assume_abort_if_not(var_1_4 >= 0);
 assume_abort_if_not(var_1_4 <= 65535);
 var_1_5 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_5 >= 0);
 assume_abort_if_not(var_1_5 <= 1);
 var_1_8 = __VERIFIER_nondet_short();
 assume_abort_if_not(var_1_8 >= -32767);
 assume_abort_if_not(var_1_8 <= 32766);
 var_1_9 = __VERIFIER_nondet_short();
 assume_abort_if_not(var_1_9 >= 0);
 assume_abort_if_not(var_1_9 <= 16383);
 var_1_10 = __VERIFIER_nondet_short();
 assume_abort_if_not(var_1_10 >= 0);
 assume_abort_if_not(var_1_10 <= 16383);
 var_1_11 = __VERIFIER_nondet_short();
 assume_abort_if_not(var_1_11 >= -16383);
 assume_abort_if_not(var_1_11 <= 16383);
 var_1_13 = __VERIFIER_nondet_double();
 assume_abort_if_not((var_1_13 >= -461168.6018427383000e+13F && var_1_13 <= -1.0e-20F) || (var_1_13 <= 4611686.018427383000e+12F && var_1_13 >= 1.0e-20F ));
 var_1_14 = __VERIFIER_nondet_double();
 assume_abort_if_not((var_1_14 >= -461168.6018427383000e+13F && var_1_14 <= -1.0e-20F) || (var_1_14 <= 4611686.018427383000e+12F && var_1_14 >= 1.0e-20F ));
 var_1_17 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_17 >= 1);
 assume_abort_if_not(var_1_17 <= 1);
 var_1_18 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_18 >= 1);
 assume_abort_if_not(var_1_18 <= 1);
 var_1_20 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_20 >= -128);
 assume_abort_if_not(var_1_20 <= 127);
 assume_abort_if_not(var_1_20 != 0);
 var_1_21 = __VERIFIER_nondet_float();
 assume_abort_if_not((var_1_21 >= 0.0F && var_1_21 <= -1.0e-20F) || (var_1_21 <= 4611686.018427383000e+12F && var_1_21 >= 1.0e-20F ));
 var_1_24 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_24 >= -1);
 assume_abort_if_not(var_1_24 <= 126);
 var_1_25 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_25 >= 0);
 assume_abort_if_not(var_1_25 <= 126);
 var_1_27 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_27 >= 0);
 assume_abort_if_not(var_1_27 <= 0);
}
void updateLastVariables(void) {
 last_1_var_1_22 = var_1_22;
}
int property(void) {
 return (((((((((var_1_2 == (var_1_3 ^ var_1_4)) ? ((var_1_15 && var_1_26) ? (var_1_1 == ((signed long int) var_1_2)) : (var_1_1 == ((signed long int) (((((var_1_2 + var_1_3)) < (var_1_4)) ? ((var_1_2 + var_1_3)) : (var_1_4)))))) : 1) && (var_1_7 == ((signed short int) ((((var_1_8) < (((var_1_9 - var_1_10) + var_1_11))) ? (var_1_8) : (((var_1_9 - var_1_10) + var_1_11))))))) && ((((var_1_22 * var_1_9) <= var_1_1) || var_1_15) ? (var_1_12 == ((double) (var_1_13 + var_1_14))) : 1)) && ((var_1_8 >= last_1_var_1_22) ? (var_1_15 == ((unsigned char) (var_1_17 && var_1_18))) : 1)) && (((var_1_22 / var_1_20) <= var_1_22) ? (var_1_26 ? (var_1_19 == ((float) ((var_1_21 + ((((var_1_13) < 0 ) ? -(var_1_13) : (var_1_13)))) - (((((((1000000.625f) < 0 ) ? -(1000000.625f) : (1000000.625f))) < 0 ) ? -((((1000000.625f) < 0 ) ? -(1000000.625f) : (1000000.625f))) : ((((1000000.625f) < 0 ) ? -(1000000.625f) : (1000000.625f)))))))) : (var_1_19 == ((float) var_1_13))) : 1)) && ((var_1_18 || (var_1_5 && var_1_15)) ? (var_1_22 == ((unsigned long int) var_1_1)) : 1)) && ((var_1_17 && var_1_26) ? (var_1_23 == ((signed char) (var_1_24 - var_1_25))) : 1)) && (var_1_26 == ((unsigned char) (var_1_17 && var_1_27)))) && ((var_1_21 < var_1_12) ? ((var_1_11 >= ((((var_1_4) < (var_1_7)) ? (var_1_4) : (var_1_7)))) ? (var_1_17 ? (var_1_28 == ((unsigned char) var_1_25)) : (var_1_28 == ((unsigned char) 32))) : 1) : (var_1_28 == ((unsigned char) var_1_25)))
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
