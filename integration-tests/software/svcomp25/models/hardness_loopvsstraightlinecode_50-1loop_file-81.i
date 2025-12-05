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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch8150_1loop.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
unsigned char var_1_1 = 5;
unsigned char var_1_5 = 128;
unsigned char var_1_6 = 4;
unsigned char var_1_7 = 10;
unsigned char var_1_8 = 0;
unsigned char var_1_9 = 1;
unsigned long int var_1_10 = 0;
unsigned short int var_1_11 = 4;
unsigned short int var_1_12 = 54828;
unsigned short int var_1_13 = 61894;
unsigned short int var_1_14 = 10000;
unsigned short int var_1_15 = 10000;
signed short int var_1_16 = 0;
signed char var_1_17 = 32;
signed char var_1_18 = 64;
signed char var_1_19 = 10;
signed char var_1_20 = 8;
signed char var_1_21 = 5;
signed char var_1_22 = 2;
signed char var_1_23 = 64;
signed long int var_1_24 = -5;
unsigned char last_1_var_1_1 = 5;
unsigned char last_1_var_1_7 = 10;
unsigned short int last_1_var_1_11 = 4;
signed char last_1_var_1_17 = 32;
void initially(void) {
}
void step(void) {
 var_1_16 = (last_1_var_1_17 - 1);
 unsigned char stepLocal_2 = var_1_8;
 unsigned char stepLocal_1 = var_1_8;
 if (((var_1_6 / var_1_5) != ((((var_1_16) < (last_1_var_1_7)) ? (var_1_16) : (last_1_var_1_7)))) && stepLocal_1) {
  var_1_7 = var_1_5;
 } else {
  if ((last_1_var_1_7 > var_1_5) || stepLocal_2) {
   var_1_7 = var_1_5;
  } else {
   var_1_7 = var_1_6;
  }
 }
 if (var_1_16 > ((((var_1_7) > (var_1_5)) ? (var_1_7) : (var_1_5)))) {
  var_1_17 = (var_1_18 - var_1_19);
 } else {
  var_1_17 = (var_1_20 - (var_1_21 + var_1_22));
 }
 signed long int stepLocal_0 = var_1_7 + var_1_16;
 if (last_1_var_1_1 != stepLocal_0) {
  var_1_1 = (var_1_5 - ((((0) < (var_1_6)) ? (0) : (var_1_6))));
 }
 if (! var_1_9) {
  var_1_10 = ((((var_1_1) < (var_1_5)) ? (var_1_1) : (var_1_5)));
 }
 if (var_1_8) {
  var_1_11 = (((((var_1_12) > (var_1_13)) ? (var_1_12) : (var_1_13))) - ((var_1_14 + var_1_15) - last_1_var_1_11));
 }
 var_1_24 = var_1_12;
 if (! ((var_1_13 & var_1_7) != var_1_24)) {
  var_1_23 = ((((var_1_20) < ((((((var_1_21 + -4)) < (var_1_22)) ? ((var_1_21 + -4)) : (var_1_22))))) ? (var_1_20) : ((((((var_1_21 + -4)) < (var_1_22)) ? ((var_1_21 + -4)) : (var_1_22))))));
 } else {
  if (! var_1_8) {
   var_1_23 = (var_1_22 + var_1_21);
  }
 }
}
void updateVariables() {
 var_1_5 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_5 >= 127);
 assume_abort_if_not(var_1_5 <= 254);
 var_1_6 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_6 >= 0);
 assume_abort_if_not(var_1_6 <= 127);
 var_1_8 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_8 >= 0);
 assume_abort_if_not(var_1_8 <= 1);
 var_1_9 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_9 >= 0);
 assume_abort_if_not(var_1_9 <= 1);
 var_1_12 = __VERIFIER_nondet_ushort();
 assume_abort_if_not(var_1_12 >= 32767);
 assume_abort_if_not(var_1_12 <= 65534);
 var_1_13 = __VERIFIER_nondet_ushort();
 assume_abort_if_not(var_1_13 >= 32767);
 assume_abort_if_not(var_1_13 <= 65534);
 var_1_14 = __VERIFIER_nondet_ushort();
 assume_abort_if_not(var_1_14 >= 8191);
 assume_abort_if_not(var_1_14 <= 16384);
 var_1_15 = __VERIFIER_nondet_ushort();
 assume_abort_if_not(var_1_15 >= 8192);
 assume_abort_if_not(var_1_15 <= 16383);
 var_1_18 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_18 >= -1);
 assume_abort_if_not(var_1_18 <= 126);
 var_1_19 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_19 >= 0);
 assume_abort_if_not(var_1_19 <= 126);
 var_1_20 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_20 >= -1);
 assume_abort_if_not(var_1_20 <= 126);
 var_1_21 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_21 >= 0);
 assume_abort_if_not(var_1_21 <= 63);
 var_1_22 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_22 >= 0);
 assume_abort_if_not(var_1_22 <= 63);
}
void updateLastVariables() {
 last_1_var_1_1 = var_1_1;
 last_1_var_1_7 = var_1_7;
 last_1_var_1_11 = var_1_11;
 last_1_var_1_17 = var_1_17;
}
int property() {
 return ((((((((last_1_var_1_1 != (var_1_7 + var_1_16)) ? (var_1_1 == ((unsigned char) (var_1_5 - ((((0) < (var_1_6)) ? (0) : (var_1_6)))))) : 1) && ((((var_1_6 / var_1_5) != ((((var_1_16) < (last_1_var_1_7)) ? (var_1_16) : (last_1_var_1_7)))) && var_1_8) ? (var_1_7 == ((unsigned char) var_1_5)) : (((last_1_var_1_7 > var_1_5) || var_1_8) ? (var_1_7 == ((unsigned char) var_1_5)) : (var_1_7 == ((unsigned char) var_1_6))))) && ((! var_1_9) ? (var_1_10 == ((unsigned long int) ((((var_1_1) < (var_1_5)) ? (var_1_1) : (var_1_5))))) : 1)) && (var_1_8 ? (var_1_11 == ((unsigned short int) (((((var_1_12) > (var_1_13)) ? (var_1_12) : (var_1_13))) - ((var_1_14 + var_1_15) - last_1_var_1_11)))) : 1)) && (var_1_16 == ((signed short int) (last_1_var_1_17 - 1)))) && ((var_1_16 > ((((var_1_7) > (var_1_5)) ? (var_1_7) : (var_1_5)))) ? (var_1_17 == ((signed char) (var_1_18 - var_1_19))) : (var_1_17 == ((signed char) (var_1_20 - (var_1_21 + var_1_22)))))) && ((! ((var_1_13 & var_1_7) != var_1_24)) ? (var_1_23 == ((signed char) ((((var_1_20) < ((((((var_1_21 + -4)) < (var_1_22)) ? ((var_1_21 + -4)) : (var_1_22))))) ? (var_1_20) : ((((((var_1_21 + -4)) < (var_1_22)) ? ((var_1_21 + -4)) : (var_1_22)))))))) : ((! var_1_8) ? (var_1_23 == ((signed char) (var_1_22 + var_1_21))) : 1))) && (var_1_24 == ((signed long int) var_1_12))
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
