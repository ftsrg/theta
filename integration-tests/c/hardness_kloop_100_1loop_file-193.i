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
void reach_error(void) { __assert_fail("0", "Req1_Prop1_Batch193100_1loop.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
void initially(void);
void step(void);
void updateVariables(void);
void updateLastVariables(void);
int property(void);
int main(void);
unsigned char isInitial = 0;
unsigned char var_1_1 = 1;
unsigned char var_1_4 = 0;
unsigned short int var_1_5 = 2;
unsigned short int var_1_6 = 25;
unsigned short int var_1_7 = 100;
signed long int var_1_8 = 0;
float var_1_9 = 8.25;
signed char var_1_10 = -128;
float var_1_11 = 5.5;
float var_1_12 = 0.0;
float var_1_13 = 0.8;
double var_1_14 = 1.625;
signed char var_1_15 = -1;
unsigned char var_1_16 = 1;
unsigned char var_1_17 = 0;
unsigned char var_1_18 = 1;
unsigned char var_1_19 = 0;
unsigned char var_1_20 = 0;
unsigned char var_1_21 = 128;
unsigned char var_1_22 = 5;
unsigned char var_1_23 = 4;
float var_1_24 = 3.7;
unsigned char var_1_25 = 16;
unsigned char var_1_26 = 0;
unsigned char var_1_27 = 0;
unsigned char var_1_28 = 0;
unsigned char var_1_29 = 0;
double var_1_30 = 255.25;
double var_1_31 = 256.4;
double var_1_32 = 100.6;
double var_1_33 = 25.2;
double var_1_34 = 0.3;
signed long int var_1_35 = 0;
unsigned short int last_1_var_1_5 = 2;
signed long int last_1_var_1_35 = 0;
void initially(void) {
}
void step(void) {
 unsigned short int stepLocal_2 = var_1_7;
 if (last_1_var_1_35 >= stepLocal_2) {
  var_1_8 = (var_1_7 + last_1_var_1_5);
 } else {
  var_1_8 = (var_1_6 - last_1_var_1_5);
 }
 if (var_1_4) {
  var_1_5 = ((((var_1_6) > (((((var_1_7) < 0 ) ? -(var_1_7) : (var_1_7))))) ? (var_1_6) : (((((var_1_7) < 0 ) ? -(var_1_7) : (var_1_7))))));
 }
 if (var_1_4) {
  var_1_16 = var_1_17;
 } else {
  var_1_16 = ((var_1_18 && var_1_19) && var_1_20);
 }
 if (var_1_13 >= var_1_11) {
  var_1_21 = (var_1_22 + 8);
 } else {
  var_1_21 = ((((var_1_22) < (var_1_23)) ? (var_1_22) : (var_1_23)));
 }
 var_1_24 = ((((var_1_13) < (var_1_11)) ? (var_1_13) : (var_1_11)));
 signed long int stepLocal_5 = (((var_1_5) > ((var_1_15 / var_1_10))) ? (var_1_5) : ((var_1_15 / var_1_10)));
 signed long int stepLocal_4 = (var_1_22 + var_1_23) - var_1_5;
 if (stepLocal_4 <= (var_1_8 / ((((var_1_15) < (var_1_10)) ? (var_1_15) : (var_1_10))))) {
  if (stepLocal_5 < var_1_8) {
   var_1_25 = var_1_23;
  } else {
   var_1_25 = 1;
  }
 } else {
  var_1_25 = 16;
 }
 signed long int stepLocal_6 = (((var_1_25) < (var_1_21)) ? (var_1_25) : (var_1_21));
 if ((32 ^ var_1_5) > stepLocal_6) {
  var_1_26 = (var_1_17 || ((var_1_27 || var_1_28) || var_1_29));
 }
 unsigned short int stepLocal_1 = var_1_5;
 signed long int stepLocal_0 = var_1_8;
 if (var_1_5 == stepLocal_0) {
  var_1_1 = (! var_1_4);
 } else {
  if (var_1_8 < stepLocal_1) {
   var_1_1 = var_1_4;
  }
 }
 if (var_1_7 > (var_1_5 * var_1_8)) {
  var_1_14 = ((((255.375) < 0 ) ? -(255.375) : (255.375)));
 } else {
  if (var_1_10 < (5 / var_1_15)) {
   var_1_14 = var_1_11;
  } else {
   var_1_14 = var_1_12;
  }
 }
 if (var_1_13 <= (- var_1_14)) {
  if (! var_1_18) {
   var_1_30 = ((var_1_13 - 255.6) + var_1_31);
  } else {
   var_1_30 = ((var_1_12 - 8.65) - (var_1_13 + var_1_32));
  }
 } else {
  if ((var_1_8 / var_1_10) == var_1_7) {
   var_1_30 = (((((((((var_1_31) > (var_1_32)) ? (var_1_31) : (var_1_32))) + var_1_13)) > (((var_1_12 - var_1_33) - (5.645110326468543E18 - var_1_34)))) ? ((((((var_1_31) > (var_1_32)) ? (var_1_31) : (var_1_32))) + var_1_13)) : (((var_1_12 - var_1_33) - (5.645110326468543E18 - var_1_34)))));
  }
 }
 if ((var_1_6 <= (var_1_8 | var_1_22)) || ((- var_1_30) < var_1_34)) {
  if (var_1_32 <= var_1_13) {
   var_1_35 = var_1_10;
  } else {
   var_1_35 = var_1_8;
  }
 } else {
  var_1_35 = var_1_8;
 }
 signed long int stepLocal_3 = var_1_35;
 if ((var_1_5 / var_1_10) <= stepLocal_3) {
  var_1_9 = (var_1_11 - (var_1_12 - var_1_13));
 }
}
void updateVariables(void) {
 var_1_4 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_4 >= 1);
 assume_abort_if_not(var_1_4 <= 1);
 var_1_6 = __VERIFIER_nondet_ushort();
 assume_abort_if_not(var_1_6 >= 0);
 assume_abort_if_not(var_1_6 <= 65534);
 var_1_7 = __VERIFIER_nondet_ushort();
 assume_abort_if_not(var_1_7 >= 0);
 assume_abort_if_not(var_1_7 <= 65534);
 var_1_10 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_10 >= -128);
 assume_abort_if_not(var_1_10 <= 127);
 assume_abort_if_not(var_1_10 != 0);
 var_1_11 = __VERIFIER_nondet_float();
 assume_abort_if_not((var_1_11 >= 0.0F && var_1_11 <= -1.0e-20F) || (var_1_11 <= 9223372.036854766000e+12F && var_1_11 >= 1.0e-20F ));
 var_1_12 = __VERIFIER_nondet_float();
 assume_abort_if_not((var_1_12 >= 4611686.018427383000e+12F && var_1_12 <= -1.0e-20F) || (var_1_12 <= 9223372.036854766000e+12F && var_1_12 >= 1.0e-20F ));
 var_1_13 = __VERIFIER_nondet_float();
 assume_abort_if_not((var_1_13 >= 0.0F && var_1_13 <= -1.0e-20F) || (var_1_13 <= 4611686.018427383000e+12F && var_1_13 >= 1.0e-20F ));
 var_1_15 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_15 >= -128);
 assume_abort_if_not(var_1_15 <= 127);
 assume_abort_if_not(var_1_15 != 0);
 var_1_17 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_17 >= 0);
 assume_abort_if_not(var_1_17 <= 0);
 var_1_18 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_18 >= 1);
 assume_abort_if_not(var_1_18 <= 1);
 var_1_19 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_19 >= 1);
 assume_abort_if_not(var_1_19 <= 1);
 var_1_20 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_20 >= 1);
 assume_abort_if_not(var_1_20 <= 1);
 var_1_22 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_22 >= 0);
 assume_abort_if_not(var_1_22 <= 127);
 var_1_23 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_23 >= 0);
 assume_abort_if_not(var_1_23 <= 254);
 var_1_27 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_27 >= 0);
 assume_abort_if_not(var_1_27 <= 0);
 var_1_28 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_28 >= 0);
 assume_abort_if_not(var_1_28 <= 0);
 var_1_29 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_29 >= 0);
 assume_abort_if_not(var_1_29 <= 0);
 var_1_31 = __VERIFIER_nondet_double();
 assume_abort_if_not((var_1_31 >= -461168.6018427383000e+13F && var_1_31 <= -1.0e-20F) || (var_1_31 <= 4611686.018427383000e+12F && var_1_31 >= 1.0e-20F ));
 var_1_32 = __VERIFIER_nondet_double();
 assume_abort_if_not((var_1_32 >= 0.0F && var_1_32 <= -1.0e-20F) || (var_1_32 <= 4611686.018427383000e+12F && var_1_32 >= 1.0e-20F ));
 var_1_33 = __VERIFIER_nondet_double();
 assume_abort_if_not((var_1_33 >= 0.0F && var_1_33 <= -1.0e-20F) || (var_1_33 <= 4611686.018427383000e+12F && var_1_33 >= 1.0e-20F ));
 var_1_34 = __VERIFIER_nondet_double();
 assume_abort_if_not((var_1_34 >= 0.0F && var_1_34 <= -1.0e-20F) || (var_1_34 <= 4611686.018427383000e+12F && var_1_34 >= 1.0e-20F ));
}
void updateLastVariables(void) {
 last_1_var_1_5 = var_1_5;
 last_1_var_1_35 = var_1_35;
}
int property(void) {
 return ((((((((((((var_1_5 == var_1_8) ? (var_1_1 == ((unsigned char) (! var_1_4))) : ((var_1_8 < var_1_5) ? (var_1_1 == ((unsigned char) var_1_4)) : 1)) && (var_1_4 ? (var_1_5 == ((unsigned short int) ((((var_1_6) > (((((var_1_7) < 0 ) ? -(var_1_7) : (var_1_7))))) ? (var_1_6) : (((((var_1_7) < 0 ) ? -(var_1_7) : (var_1_7)))))))) : 1)) && ((last_1_var_1_35 >= var_1_7) ? (var_1_8 == ((signed long int) (var_1_7 + last_1_var_1_5))) : (var_1_8 == ((signed long int) (var_1_6 - last_1_var_1_5))))) && (((var_1_5 / var_1_10) <= var_1_35) ? (var_1_9 == ((float) (var_1_11 - (var_1_12 - var_1_13)))) : 1)) && ((var_1_7 > (var_1_5 * var_1_8)) ? (var_1_14 == ((double) ((((255.375) < 0 ) ? -(255.375) : (255.375))))) : ((var_1_10 < (5 / var_1_15)) ? (var_1_14 == ((double) var_1_11)) : (var_1_14 == ((double) var_1_12))))) && (var_1_4 ? (var_1_16 == ((unsigned char) var_1_17)) : (var_1_16 == ((unsigned char) ((var_1_18 && var_1_19) && var_1_20))))) && ((var_1_13 >= var_1_11) ? (var_1_21 == ((unsigned char) (var_1_22 + 8))) : (var_1_21 == ((unsigned char) ((((var_1_22) < (var_1_23)) ? (var_1_22) : (var_1_23))))))) && (var_1_24 == ((float) ((((var_1_13) < (var_1_11)) ? (var_1_13) : (var_1_11)))))) && ((((var_1_22 + var_1_23) - var_1_5) <= (var_1_8 / ((((var_1_15) < (var_1_10)) ? (var_1_15) : (var_1_10))))) ? ((((((var_1_5) > ((var_1_15 / var_1_10))) ? (var_1_5) : ((var_1_15 / var_1_10)))) < var_1_8) ? (var_1_25 == ((unsigned char) var_1_23)) : (var_1_25 == ((unsigned char) 1))) : (var_1_25 == ((unsigned char) 16)))) && (((32 ^ var_1_5) > ((((var_1_25) < (var_1_21)) ? (var_1_25) : (var_1_21)))) ? (var_1_26 == ((unsigned char) (var_1_17 || ((var_1_27 || var_1_28) || var_1_29)))) : 1)) && ((var_1_13 <= (- var_1_14)) ? ((! var_1_18) ? (var_1_30 == ((double) ((var_1_13 - 255.6) + var_1_31))) : (var_1_30 == ((double) ((var_1_12 - 8.65) - (var_1_13 + var_1_32))))) : (((var_1_8 / var_1_10) == var_1_7) ? (var_1_30 == ((double) (((((((((var_1_31) > (var_1_32)) ? (var_1_31) : (var_1_32))) + var_1_13)) > (((var_1_12 - var_1_33) - (5.645110326468543E18 - var_1_34)))) ? ((((((var_1_31) > (var_1_32)) ? (var_1_31) : (var_1_32))) + var_1_13)) : (((var_1_12 - var_1_33) - (5.645110326468543E18 - var_1_34))))))) : 1))) && (((var_1_6 <= (var_1_8 | var_1_22)) || ((- var_1_30) < var_1_34)) ? ((var_1_32 <= var_1_13) ? (var_1_35 == ((signed long int) var_1_10)) : (var_1_35 == ((signed long int) var_1_8))) : (var_1_35 == ((signed long int) var_1_8)))
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
