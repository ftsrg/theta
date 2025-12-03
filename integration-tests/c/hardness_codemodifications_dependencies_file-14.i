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
void reach_error(void) { __assert_fail("0", "Req1_Prop1_Batch14dependencies.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
void initially(void);
void step(void);
void updateVariables(void);
void updateLastVariables(void);
int property(void);
int main(void);
unsigned char isInitial = 0;
signed long int var_1_1 = -10;
signed long int var_1_2 = -256;
signed long int var_1_3 = 100;
unsigned char var_1_4 = 0;
unsigned char var_1_7 = 1;
unsigned char var_1_8 = 0;
unsigned char var_1_9 = 0;
unsigned char var_1_10 = 1;
unsigned long int var_1_11 = 16;
signed short int var_1_12 = -32;
unsigned long int var_1_13 = 100000000;
unsigned long int var_1_14 = 25;
unsigned char var_1_15 = 8;
unsigned char var_1_17 = 100;
unsigned char var_1_18 = 10;
signed long int var_1_19 = 1;
unsigned char var_1_20 = 5;
float var_1_21 = 25.5;
signed long int var_1_23 = -5;
float var_1_24 = 1.125;
float var_1_25 = 15.25;
signed long int var_1_26 = 5;
unsigned char var_1_28 = 16;
unsigned long int last_1_var_1_11 = 16;
float last_1_var_1_21 = 25.5;
void initially(void) {
}
void step(void) {
 if ((last_1_var_1_21 + 9.999999999999994E14f) < (- last_1_var_1_21)) {
  var_1_4 = (var_1_7 && var_1_8);
 } else {
  if (var_1_7) {
   var_1_4 = ((var_1_8 || var_1_9) && var_1_10);
  }
 }
 var_1_1 = (var_1_2 + var_1_3);
 if ((var_1_3 / var_1_12) <= last_1_var_1_11) {
  var_1_11 = ((((var_1_13) > (var_1_14)) ? (var_1_13) : (var_1_14)));
 }
 var_1_28 = var_1_17;
 if ((var_1_13 % var_1_20) != var_1_11) {
  if (var_1_18 == var_1_17) {
   if (var_1_4) {
    var_1_19 = var_1_18;
   } else {
    var_1_19 = var_1_11;
   }
  }
 }
 if (var_1_9 || ((var_1_11 + var_1_19) <= 4)) {
  var_1_26 = (var_1_19 - var_1_20);
 } else {
  var_1_26 = (var_1_20 - var_1_17);
 }
 if (((~ var_1_1) * var_1_26) >= (var_1_3 % var_1_23)) {
  var_1_21 = ((((var_1_24) > (var_1_25)) ? (var_1_24) : (var_1_25)));
 }
 if (((((var_1_21) < (-0.5)) ? (var_1_21) : (-0.5))) > (10.9 * var_1_21)) {
  if (var_1_4) {
   var_1_15 = ((((((((var_1_17) < 0 ) ? -(var_1_17) : (var_1_17)))) < (var_1_18)) ? (((((var_1_17) < 0 ) ? -(var_1_17) : (var_1_17)))) : (var_1_18)));
  } else {
   var_1_15 = var_1_18;
  }
 }
}
void updateVariables(void) {
 var_1_2 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_2 >= -1073741823);
 assume_abort_if_not(var_1_2 <= 1073741823);
 var_1_3 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_3 >= -1073741823);
 assume_abort_if_not(var_1_3 <= 1073741823);
 var_1_7 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_7 >= 0);
 assume_abort_if_not(var_1_7 <= 1);
 var_1_8 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_8 >= 0);
 assume_abort_if_not(var_1_8 <= 0);
 var_1_9 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_9 >= 1);
 assume_abort_if_not(var_1_9 <= 1);
 var_1_10 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_10 >= 1);
 assume_abort_if_not(var_1_10 <= 1);
 var_1_12 = __VERIFIER_nondet_short();
 assume_abort_if_not(var_1_12 >= -32768);
 assume_abort_if_not(var_1_12 <= 32767);
 assume_abort_if_not(var_1_12 != 0);
 var_1_13 = __VERIFIER_nondet_ulong();
 assume_abort_if_not(var_1_13 >= 0);
 assume_abort_if_not(var_1_13 <= 4294967294);
 var_1_14 = __VERIFIER_nondet_ulong();
 assume_abort_if_not(var_1_14 >= 0);
 assume_abort_if_not(var_1_14 <= 4294967294);
 var_1_17 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_17 >= 0);
 assume_abort_if_not(var_1_17 <= 254);
 var_1_18 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_18 >= 0);
 assume_abort_if_not(var_1_18 <= 254);
 var_1_20 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_20 >= 0);
 assume_abort_if_not(var_1_20 <= 255);
 assume_abort_if_not(var_1_20 != 0);
 var_1_23 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_23 >= -2147483648);
 assume_abort_if_not(var_1_23 <= 2147483647);
 assume_abort_if_not(var_1_23 != 0);
 var_1_24 = __VERIFIER_nondet_float();
 assume_abort_if_not((var_1_24 >= -922337.2036854766000e+13F && var_1_24 <= -1.0e-20F) || (var_1_24 <= 9223372.036854766000e+12F && var_1_24 >= 1.0e-20F ));
 var_1_25 = __VERIFIER_nondet_float();
 assume_abort_if_not((var_1_25 >= -922337.2036854766000e+13F && var_1_25 <= -1.0e-20F) || (var_1_25 <= 9223372.036854766000e+12F && var_1_25 >= 1.0e-20F ));
}
void updateLastVariables(void) {
 last_1_var_1_11 = var_1_11;
 last_1_var_1_21 = var_1_21;
}
int property(void) {
 return (((((((var_1_1 == ((signed long int) (var_1_2 + var_1_3))) && (((last_1_var_1_21 + 9.999999999999994E14f) < (- last_1_var_1_21)) ? (var_1_4 == ((unsigned char) (var_1_7 && var_1_8))) : (var_1_7 ? (var_1_4 == ((unsigned char) ((var_1_8 || var_1_9) && var_1_10))) : 1))) && (((var_1_3 / var_1_12) <= last_1_var_1_11) ? (var_1_11 == ((unsigned long int) ((((var_1_13) > (var_1_14)) ? (var_1_13) : (var_1_14))))) : 1)) && ((((((var_1_21) < (-0.5)) ? (var_1_21) : (-0.5))) > (10.9 * var_1_21)) ? (var_1_4 ? (var_1_15 == ((unsigned char) ((((((((var_1_17) < 0 ) ? -(var_1_17) : (var_1_17)))) < (var_1_18)) ? (((((var_1_17) < 0 ) ? -(var_1_17) : (var_1_17)))) : (var_1_18))))) : (var_1_15 == ((unsigned char) var_1_18))) : 1)) && (((var_1_13 % var_1_20) != var_1_11) ? ((var_1_18 == var_1_17) ? (var_1_4 ? (var_1_19 == ((signed long int) var_1_18)) : (var_1_19 == ((signed long int) var_1_11))) : 1) : 1)) && ((((~ var_1_1) * var_1_26) >= (var_1_3 % var_1_23)) ? (var_1_21 == ((float) ((((var_1_24) > (var_1_25)) ? (var_1_24) : (var_1_25))))) : 1)) && ((var_1_9 || ((var_1_11 + var_1_19) <= 4)) ? (var_1_26 == ((signed long int) (var_1_19 - var_1_20))) : (var_1_26 == ((signed long int) (var_1_20 - var_1_17))))) && (var_1_28 == ((unsigned char) var_1_17))
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
