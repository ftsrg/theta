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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch81no_floats.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
signed long int var_1_1 = 9999;
unsigned char var_1_2 = 1;
signed long int var_1_3 = 4;
signed long int var_1_4 = 2;
signed long int var_1_5 = 0;
signed long int var_1_6 = 999999999;
signed char var_1_7 = -128;
signed char var_1_11 = 16;
signed char var_1_12 = 16;
unsigned short int var_1_13 = 5;
unsigned char var_1_14 = 1;
unsigned short int var_1_15 = 16;
unsigned short int var_1_16 = 32647;
unsigned short int var_1_17 = 128;
signed long int var_1_18 = -8;
unsigned short int last_1_var_1_13 = 5;
signed long int last_1_var_1_18 = -8;
void initially(void) {
}
void step(void) {
 signed long int stepLocal_0 = (((-25) < (last_1_var_1_18)) ? (-25) : (last_1_var_1_18));
 if (stepLocal_0 != (last_1_var_1_18 ^ last_1_var_1_13)) {
  if (var_1_2) {
   var_1_7 = (var_1_11 + var_1_12);
  }
 } else {
  var_1_7 = ((((var_1_12) < (var_1_11)) ? (var_1_12) : (var_1_11)));
 }
 unsigned char stepLocal_1 = var_1_11 >= var_1_7;
 if (stepLocal_1 && var_1_14) {
  var_1_13 = ((((var_1_15) < (100)) ? (var_1_15) : (100)));
 } else {
  var_1_13 = ((var_1_16 - 5) + var_1_17);
 }
 signed char stepLocal_2 = var_1_7;
 if (stepLocal_2 > var_1_16) {
  if (var_1_3 < (var_1_5 - var_1_6)) {
   var_1_18 = ((((var_1_15) < 0 ) ? -(var_1_15) : (var_1_15)));
  } else {
   var_1_18 = var_1_13;
  }
 } else {
  var_1_18 = var_1_15;
 }
 if (var_1_2) {
  var_1_1 = ((((var_1_3) > ((var_1_4 - (var_1_5 - var_1_6)))) ? (var_1_3) : ((var_1_4 - (var_1_5 - var_1_6)))));
 }
}
void updateVariables() {
 var_1_2 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_2 >= 0);
 assume_abort_if_not(var_1_2 <= 1);
 var_1_3 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_3 >= -2147483648);
 assume_abort_if_not(var_1_3 <= 2147483647);
 var_1_4 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_4 >= 0);
 assume_abort_if_not(var_1_4 <= 2147483647);
 var_1_5 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_5 >= 2147483647);
 assume_abort_if_not(var_1_5 <= 2147483647);
 var_1_6 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_6 >= 0);
 assume_abort_if_not(var_1_6 <= 2147483647);
 var_1_11 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_11 >= -63);
 assume_abort_if_not(var_1_11 <= 63);
 var_1_12 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_12 >= -63);
 assume_abort_if_not(var_1_12 <= 63);
 var_1_14 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_14 >= 0);
 assume_abort_if_not(var_1_14 <= 1);
 var_1_15 = __VERIFIER_nondet_ushort();
 assume_abort_if_not(var_1_15 >= 0);
 assume_abort_if_not(var_1_15 <= 65534);
 var_1_16 = __VERIFIER_nondet_ushort();
 assume_abort_if_not(var_1_16 >= 16383);
 assume_abort_if_not(var_1_16 <= 32767);
 var_1_17 = __VERIFIER_nondet_ushort();
 assume_abort_if_not(var_1_17 >= 0);
 assume_abort_if_not(var_1_17 <= 32767);
}
void updateLastVariables() {
 last_1_var_1_13 = var_1_13;
 last_1_var_1_18 = var_1_18;
}
int property() {
 return (((var_1_2 ? (var_1_1 == ((signed long int) ((((var_1_3) > ((var_1_4 - (var_1_5 - var_1_6)))) ? (var_1_3) : ((var_1_4 - (var_1_5 - var_1_6))))))) : 1) && ((((((-25) < (last_1_var_1_18)) ? (-25) : (last_1_var_1_18))) != (last_1_var_1_18 ^ last_1_var_1_13)) ? (var_1_2 ? (var_1_7 == ((signed char) (var_1_11 + var_1_12))) : 1) : (var_1_7 == ((signed char) ((((var_1_12) < (var_1_11)) ? (var_1_12) : (var_1_11))))))) && (((var_1_11 >= var_1_7) && var_1_14) ? (var_1_13 == ((unsigned short int) ((((var_1_15) < (100)) ? (var_1_15) : (100))))) : (var_1_13 == ((unsigned short int) ((var_1_16 - 5) + var_1_17))))) && ((var_1_7 > var_1_16) ? ((var_1_3 < (var_1_5 - var_1_6)) ? (var_1_18 == ((signed long int) ((((var_1_15) < 0 ) ? -(var_1_15) : (var_1_15))))) : (var_1_18 == ((signed long int) var_1_13))) : (var_1_18 == ((signed long int) var_1_15)))
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
