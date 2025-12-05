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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch86no_floats.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
signed short int var_1_1 = 0;
unsigned char var_1_2 = 0;
signed short int var_1_3 = 2;
signed short int var_1_4 = 256;
signed short int var_1_5 = -256;
signed short int var_1_6 = 2;
signed long int var_1_7 = 255;
signed long int var_1_8 = 127;
signed long int var_1_9 = 128;
signed long int var_1_10 = 499;
unsigned short int var_1_11 = 10;
unsigned char var_1_12 = 1;
unsigned short int var_1_13 = 8;
unsigned short int var_1_14 = 256;
unsigned short int var_1_15 = 1;
unsigned short int var_1_16 = 16;
unsigned short int var_1_17 = 57705;
unsigned long int var_1_18 = 64;
void initially(void) {
}
void step(void) {
 if (! var_1_2) {
  var_1_1 = (((((var_1_3 + (var_1_4 + var_1_5))) < (var_1_6)) ? ((var_1_3 + (var_1_4 + var_1_5))) : (var_1_6)));
 } else {
  var_1_1 = var_1_5;
 }
 signed short int stepLocal_0 = var_1_5;
 if (stepLocal_0 > 2) {
  var_1_7 = ((var_1_8 + var_1_9) - var_1_10);
 }
 var_1_18 = var_1_17;
 if (var_1_2 && var_1_12) {
  var_1_11 = (var_1_13 + ((((((((var_1_14) > (var_1_15)) ? (var_1_14) : (var_1_15)))) < (var_1_16)) ? (((((var_1_14) > (var_1_15)) ? (var_1_14) : (var_1_15)))) : (var_1_16))));
 } else {
  if (var_1_3 < (200 * (-25 << var_1_18))) {
   var_1_11 = ((((((((var_1_17 - 10000)) > (((((var_1_15) < (var_1_14)) ? (var_1_15) : (var_1_14))))) ? ((var_1_17 - 10000)) : (((((var_1_15) < (var_1_14)) ? (var_1_15) : (var_1_14)))))) < 0 ) ? -(((((var_1_17 - 10000)) > (((((var_1_15) < (var_1_14)) ? (var_1_15) : (var_1_14))))) ? ((var_1_17 - 10000)) : (((((var_1_15) < (var_1_14)) ? (var_1_15) : (var_1_14)))))) : (((((var_1_17 - 10000)) > (((((var_1_15) < (var_1_14)) ? (var_1_15) : (var_1_14))))) ? ((var_1_17 - 10000)) : (((((var_1_15) < (var_1_14)) ? (var_1_15) : (var_1_14))))))));
  } else {
   var_1_11 = (var_1_17 - var_1_15);
  }
 }
}
void updateVariables() {
 var_1_2 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_2 >= 0);
 assume_abort_if_not(var_1_2 <= 1);
 var_1_3 = __VERIFIER_nondet_short();
 assume_abort_if_not(var_1_3 >= -16383);
 assume_abort_if_not(var_1_3 <= 16383);
 var_1_4 = __VERIFIER_nondet_short();
 assume_abort_if_not(var_1_4 >= -8191);
 assume_abort_if_not(var_1_4 <= 8192);
 var_1_5 = __VERIFIER_nondet_short();
 assume_abort_if_not(var_1_5 >= -8191);
 assume_abort_if_not(var_1_5 <= 8191);
 var_1_6 = __VERIFIER_nondet_short();
 assume_abort_if_not(var_1_6 >= -32767);
 assume_abort_if_not(var_1_6 <= 32766);
 var_1_8 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_8 >= 0);
 assume_abort_if_not(var_1_8 <= 2147483647);
 var_1_9 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_9 >= 0);
 assume_abort_if_not(var_1_9 <= 2147483647);
 var_1_10 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_10 >= 0);
 assume_abort_if_not(var_1_10 <= 2147483647);
 var_1_12 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_12 >= 0);
 assume_abort_if_not(var_1_12 <= 1);
 var_1_13 = __VERIFIER_nondet_ushort();
 assume_abort_if_not(var_1_13 >= 0);
 assume_abort_if_not(var_1_13 <= 32767);
 var_1_14 = __VERIFIER_nondet_ushort();
 assume_abort_if_not(var_1_14 >= 0);
 assume_abort_if_not(var_1_14 <= 32767);
 var_1_15 = __VERIFIER_nondet_ushort();
 assume_abort_if_not(var_1_15 >= 0);
 assume_abort_if_not(var_1_15 <= 32767);
 var_1_16 = __VERIFIER_nondet_ushort();
 assume_abort_if_not(var_1_16 >= 0);
 assume_abort_if_not(var_1_16 <= 32767);
 var_1_17 = __VERIFIER_nondet_ushort();
 assume_abort_if_not(var_1_17 >= 32767);
 assume_abort_if_not(var_1_17 <= 65534);
}
void updateLastVariables() {
}
int property() {
 return ((((! var_1_2) ? (var_1_1 == ((signed short int) (((((var_1_3 + (var_1_4 + var_1_5))) < (var_1_6)) ? ((var_1_3 + (var_1_4 + var_1_5))) : (var_1_6))))) : (var_1_1 == ((signed short int) var_1_5))) && ((var_1_5 > 2) ? (var_1_7 == ((signed long int) ((var_1_8 + var_1_9) - var_1_10))) : 1)) && ((var_1_2 && var_1_12) ? (var_1_11 == ((unsigned short int) (var_1_13 + ((((((((var_1_14) > (var_1_15)) ? (var_1_14) : (var_1_15)))) < (var_1_16)) ? (((((var_1_14) > (var_1_15)) ? (var_1_14) : (var_1_15)))) : (var_1_16)))))) : ((var_1_3 < (200 * (-25 << var_1_18))) ? (var_1_11 == ((unsigned short int) ((((((((var_1_17 - 10000)) > (((((var_1_15) < (var_1_14)) ? (var_1_15) : (var_1_14))))) ? ((var_1_17 - 10000)) : (((((var_1_15) < (var_1_14)) ? (var_1_15) : (var_1_14)))))) < 0 ) ? -(((((var_1_17 - 10000)) > (((((var_1_15) < (var_1_14)) ? (var_1_15) : (var_1_14))))) ? ((var_1_17 - 10000)) : (((((var_1_15) < (var_1_14)) ? (var_1_15) : (var_1_14)))))) : (((((var_1_17 - 10000)) > (((((var_1_15) < (var_1_14)) ? (var_1_15) : (var_1_14))))) ? ((var_1_17 - 10000)) : (((((var_1_15) < (var_1_14)) ? (var_1_15) : (var_1_14)))))))))) : (var_1_11 == ((unsigned short int) (var_1_17 - var_1_15)))))) && (var_1_18 == ((unsigned long int) var_1_17))
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
