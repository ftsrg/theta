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
void reach_error(void) { __assert_fail("0", "Req1_Prop1_Batch62100_1loop.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
void initially(void);
void step(void);
void updateVariables(void);
void updateLastVariables(void);
int property(void);
int main(void);
unsigned char isInitial = 0;
double var_1_1 = 32.2;
double var_1_4 = 10000000.9;
double var_1_5 = 32.46;
double var_1_6 = 10000.6;
unsigned long int var_1_7 = 128;
signed long int var_1_8 = 100000;
unsigned long int var_1_9 = 1;
unsigned long int var_1_10 = 10000;
unsigned long int var_1_11 = 0;
unsigned char var_1_12 = 0;
unsigned char var_1_13 = 0;
unsigned char var_1_14 = 1;
unsigned char var_1_15 = 1;
unsigned char var_1_16 = 0;
double var_1_17 = 63.8;
double var_1_18 = 64.125;
double var_1_19 = 0.9;
float var_1_20 = 8.8;
float var_1_21 = 999999999999.75;
float var_1_22 = 127.5;
unsigned long int var_1_23 = 25;
float var_1_24 = 127.75;
float var_1_25 = 64.7;
signed char var_1_26 = -128;
signed char var_1_27 = 64;
unsigned long int var_1_28 = 4;
signed char var_1_30 = 25;
signed char var_1_32 = 8;
signed char var_1_33 = -1;
signed char var_1_34 = -5;
signed long int var_1_35 = -1;
unsigned char var_1_36 = 128;
unsigned char var_1_37 = 5;
unsigned long int last_1_var_1_7 = 128;
unsigned long int last_1_var_1_28 = 4;
signed long int last_1_var_1_35 = -1;
void initially(void) {
}
void step(void) {
 var_1_9 = (((((((((last_1_var_1_28) < (var_1_8)) ? (last_1_var_1_28) : (var_1_8))) + ((((last_1_var_1_35) < (var_1_10)) ? (last_1_var_1_35) : (var_1_10))))) < (var_1_11)) ? ((((((last_1_var_1_28) < (var_1_8)) ? (last_1_var_1_28) : (var_1_8))) + ((((last_1_var_1_35) < (var_1_10)) ? (last_1_var_1_35) : (var_1_10))))) : (var_1_11)));
 unsigned long int stepLocal_6 = last_1_var_1_7;
 signed char stepLocal_5 = var_1_27;
 if (stepLocal_5 > ((last_1_var_1_7 * var_1_23) + last_1_var_1_28)) {
  if (last_1_var_1_35 < stepLocal_6) {
   var_1_28 = last_1_var_1_7;
  }
 } else {
  var_1_28 = last_1_var_1_35;
 }
 signed long int stepLocal_2 = 32;
 unsigned long int stepLocal_1 = var_1_28 - var_1_8;
 if (stepLocal_2 > var_1_28) {
  if ((- var_1_9) != stepLocal_1) {
   var_1_7 = ((((((((5u) < (var_1_8)) ? (5u) : (var_1_8)))) < (var_1_9)) ? (((((5u) < (var_1_8)) ? (5u) : (var_1_8)))) : (var_1_9)));
  } else {
   var_1_7 = var_1_28;
  }
 } else {
  var_1_7 = var_1_28;
 }
 unsigned long int stepLocal_0 = var_1_9;
 if (var_1_28 >= stepLocal_0) {
  var_1_1 = ((((((((var_1_4) > (var_1_5)) ? (var_1_4) : (var_1_5))) + var_1_6) < 0 ) ? -(((((var_1_4) > (var_1_5)) ? (var_1_4) : (var_1_5))) + var_1_6) : (((((var_1_4) > (var_1_5)) ? (var_1_4) : (var_1_5))) + var_1_6)));
 } else {
  var_1_1 = (var_1_4 + var_1_5);
 }
 if (var_1_13) {
  var_1_17 = ((var_1_18 - var_1_19) + var_1_4);
 } else {
  var_1_17 = var_1_6;
 }
 if (var_1_13) {
  if (var_1_5 > var_1_18) {
   var_1_21 = ((((var_1_18) < (var_1_6)) ? (var_1_18) : (var_1_6)));
  }
 } else {
  var_1_21 = (var_1_5 + (1.55f + 5.7f));
 }
 unsigned long int stepLocal_4 = var_1_8 + (- var_1_7);
 unsigned long int stepLocal_3 = ~ var_1_28;
 if ((var_1_8 / var_1_23) == stepLocal_3) {
  if (stepLocal_4 >= var_1_10) {
   var_1_22 = ((var_1_24 + var_1_25) + (var_1_18 - ((((31.85f) > (10.5f)) ? (31.85f) : (10.5f)))));
  }
 } else {
  var_1_22 = 7.5f;
 }
 if (var_1_1 > (var_1_1 * (var_1_24 / 2.8))) {
  if (var_1_14) {
   if (var_1_13) {
    var_1_26 = ((((var_1_27) > (0)) ? (var_1_27) : (0)));
   } else {
    if (var_1_16) {
     var_1_26 = var_1_27;
    } else {
     var_1_26 = -4;
    }
   }
  } else {
   var_1_26 = var_1_27;
  }
 }
 if (var_1_4 <= (var_1_17 + (var_1_5 * var_1_6))) {
  var_1_12 = ((var_1_13 && var_1_14) && var_1_15);
 } else {
  var_1_12 = var_1_16;
 }
 if ((var_1_8 == var_1_28) || var_1_12) {
  var_1_20 = ((((25.5f) < (var_1_4)) ? (25.5f) : (var_1_4)));
 }
 if (var_1_14) {
  if (var_1_28 <= var_1_9) {
   var_1_30 = ((((var_1_32) < 0 ) ? -(var_1_32) : (var_1_32)));
  } else {
   var_1_30 = (1 + ((((1) < 0 ) ? -(1) : (1))));
  }
 } else {
  var_1_30 = (var_1_33 + var_1_34);
 }
 signed long int stepLocal_7 = -32;
 if (var_1_16) {
  var_1_35 = ((((var_1_34) < 0 ) ? -(var_1_34) : (var_1_34)));
 } else {
  if ((var_1_36 - var_1_37) <= stepLocal_7) {
   var_1_35 = var_1_28;
  } else {
   var_1_35 = var_1_30;
  }
 }
}
void updateVariables(void) {
 var_1_4 = __VERIFIER_nondet_double();
 assume_abort_if_not((var_1_4 >= -461168.6018427383000e+13F && var_1_4 <= -1.0e-20F) || (var_1_4 <= 4611686.018427383000e+12F && var_1_4 >= 1.0e-20F ));
 var_1_5 = __VERIFIER_nondet_double();
 assume_abort_if_not((var_1_5 >= -461168.6018427383000e+13F && var_1_5 <= -1.0e-20F) || (var_1_5 <= 4611686.018427383000e+12F && var_1_5 >= 1.0e-20F ));
 var_1_6 = __VERIFIER_nondet_double();
 assume_abort_if_not((var_1_6 >= -461168.6018427383000e+13F && var_1_6 <= -1.0e-20F) || (var_1_6 <= 4611686.018427383000e+12F && var_1_6 >= 1.0e-20F ));
 var_1_8 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_8 >= 0);
 assume_abort_if_not(var_1_8 <= 2147483647);
 var_1_10 = __VERIFIER_nondet_ulong();
 assume_abort_if_not(var_1_10 >= 0);
 assume_abort_if_not(var_1_10 <= 2147483647);
 var_1_11 = __VERIFIER_nondet_ulong();
 assume_abort_if_not(var_1_11 >= 0);
 assume_abort_if_not(var_1_11 <= 4294967294);
 var_1_13 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_13 >= 1);
 assume_abort_if_not(var_1_13 <= 1);
 var_1_14 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_14 >= 1);
 assume_abort_if_not(var_1_14 <= 1);
 var_1_15 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_15 >= 1);
 assume_abort_if_not(var_1_15 <= 1);
 var_1_16 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_16 >= 0);
 assume_abort_if_not(var_1_16 <= 0);
 var_1_18 = __VERIFIER_nondet_double();
 assume_abort_if_not((var_1_18 >= 0.0F && var_1_18 <= -1.0e-20F) || (var_1_18 <= 4611686.018427383000e+12F && var_1_18 >= 1.0e-20F ));
 var_1_19 = __VERIFIER_nondet_double();
 assume_abort_if_not((var_1_19 >= 0.0F && var_1_19 <= -1.0e-20F) || (var_1_19 <= 4611686.018427383000e+12F && var_1_19 >= 1.0e-20F ));
 var_1_23 = __VERIFIER_nondet_ulong();
 assume_abort_if_not(var_1_23 >= 0);
 assume_abort_if_not(var_1_23 <= 4294967295);
 assume_abort_if_not(var_1_23 != 0);
 var_1_24 = __VERIFIER_nondet_float();
 assume_abort_if_not((var_1_24 >= -230584.3009213691400e+13F && var_1_24 <= -1.0e-20F) || (var_1_24 <= 2305843.009213691400e+12F && var_1_24 >= 1.0e-20F ));
 var_1_25 = __VERIFIER_nondet_float();
 assume_abort_if_not((var_1_25 >= -230584.3009213691400e+13F && var_1_25 <= -1.0e-20F) || (var_1_25 <= 2305843.009213691400e+12F && var_1_25 >= 1.0e-20F ));
 var_1_27 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_27 >= -127);
 assume_abort_if_not(var_1_27 <= 126);
 var_1_32 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_32 >= -126);
 assume_abort_if_not(var_1_32 <= 126);
 var_1_33 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_33 >= -63);
 assume_abort_if_not(var_1_33 <= 63);
 var_1_34 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_34 >= -63);
 assume_abort_if_not(var_1_34 <= 63);
 var_1_36 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_36 >= 127);
 assume_abort_if_not(var_1_36 <= 255);
 var_1_37 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_37 >= 0);
 assume_abort_if_not(var_1_37 <= 127);
}
void updateLastVariables(void) {
 last_1_var_1_7 = var_1_7;
 last_1_var_1_28 = var_1_28;
 last_1_var_1_35 = var_1_35;
}
int property(void) {
 return ((((((((((((var_1_28 >= var_1_9) ? (var_1_1 == ((double) ((((((((var_1_4) > (var_1_5)) ? (var_1_4) : (var_1_5))) + var_1_6) < 0 ) ? -(((((var_1_4) > (var_1_5)) ? (var_1_4) : (var_1_5))) + var_1_6) : (((((var_1_4) > (var_1_5)) ? (var_1_4) : (var_1_5))) + var_1_6))))) : (var_1_1 == ((double) (var_1_4 + var_1_5)))) && ((32 > var_1_28) ? (((- var_1_9) != (var_1_28 - var_1_8)) ? (var_1_7 == ((unsigned long int) ((((((((5u) < (var_1_8)) ? (5u) : (var_1_8)))) < (var_1_9)) ? (((((5u) < (var_1_8)) ? (5u) : (var_1_8)))) : (var_1_9))))) : (var_1_7 == ((unsigned long int) var_1_28))) : (var_1_7 == ((unsigned long int) var_1_28)))) && (var_1_9 == ((unsigned long int) (((((((((last_1_var_1_28) < (var_1_8)) ? (last_1_var_1_28) : (var_1_8))) + ((((last_1_var_1_35) < (var_1_10)) ? (last_1_var_1_35) : (var_1_10))))) < (var_1_11)) ? ((((((last_1_var_1_28) < (var_1_8)) ? (last_1_var_1_28) : (var_1_8))) + ((((last_1_var_1_35) < (var_1_10)) ? (last_1_var_1_35) : (var_1_10))))) : (var_1_11)))))) && ((var_1_4 <= (var_1_17 + (var_1_5 * var_1_6))) ? (var_1_12 == ((unsigned char) ((var_1_13 && var_1_14) && var_1_15))) : (var_1_12 == ((unsigned char) var_1_16)))) && (var_1_13 ? (var_1_17 == ((double) ((var_1_18 - var_1_19) + var_1_4))) : (var_1_17 == ((double) var_1_6)))) && (((var_1_8 == var_1_28) || var_1_12) ? (var_1_20 == ((float) ((((25.5f) < (var_1_4)) ? (25.5f) : (var_1_4))))) : 1)) && (var_1_13 ? ((var_1_5 > var_1_18) ? (var_1_21 == ((float) ((((var_1_18) < (var_1_6)) ? (var_1_18) : (var_1_6))))) : 1) : (var_1_21 == ((float) (var_1_5 + (1.55f + 5.7f)))))) && (((var_1_8 / var_1_23) == (~ var_1_28)) ? (((var_1_8 + (- var_1_7)) >= var_1_10) ? (var_1_22 == ((float) ((var_1_24 + var_1_25) + (var_1_18 - ((((31.85f) > (10.5f)) ? (31.85f) : (10.5f))))))) : 1) : (var_1_22 == ((float) 7.5f)))) && ((var_1_1 > (var_1_1 * (var_1_24 / 2.8))) ? (var_1_14 ? (var_1_13 ? (var_1_26 == ((signed char) ((((var_1_27) > (0)) ? (var_1_27) : (0))))) : (var_1_16 ? (var_1_26 == ((signed char) var_1_27)) : (var_1_26 == ((signed char) -4)))) : (var_1_26 == ((signed char) var_1_27))) : 1)) && ((var_1_27 > ((last_1_var_1_7 * var_1_23) + last_1_var_1_28)) ? ((last_1_var_1_35 < last_1_var_1_7) ? (var_1_28 == ((unsigned long int) last_1_var_1_7)) : 1) : (var_1_28 == ((unsigned long int) last_1_var_1_35)))) && (var_1_14 ? ((var_1_28 <= var_1_9) ? (var_1_30 == ((signed char) ((((var_1_32) < 0 ) ? -(var_1_32) : (var_1_32))))) : (var_1_30 == ((signed char) (1 + ((((1) < 0 ) ? -(1) : (1))))))) : (var_1_30 == ((signed char) (var_1_33 + var_1_34))))) && (var_1_16 ? (var_1_35 == ((signed long int) ((((var_1_34) < 0 ) ? -(var_1_34) : (var_1_34))))) : (((var_1_36 - var_1_37) <= -32) ? (var_1_35 == ((signed long int) var_1_28)) : (var_1_35 == ((signed long int) var_1_30))))
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
