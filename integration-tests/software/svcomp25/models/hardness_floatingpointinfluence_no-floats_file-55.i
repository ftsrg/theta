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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch55no_floats.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
unsigned short int var_1_1 = 10;
unsigned char var_1_2 = 0;
unsigned char var_1_5 = 0;
signed long int var_1_7 = 256;
signed long int var_1_8 = 63;
signed long int var_1_9 = 1;
signed long int var_1_10 = 0;
signed long int var_1_11 = 16;
signed long int var_1_12 = -5;
unsigned char var_1_14 = 128;
signed long int var_1_15 = 4;
unsigned long int var_1_16 = 500;
unsigned char var_1_17 = 2;
unsigned char var_1_18 = 100;
signed long int last_1_var_1_12 = -5;
unsigned char last_1_var_1_17 = 2;
void initially(void) {
}
void step(void) {
 unsigned char stepLocal_1 = last_1_var_1_12 >= last_1_var_1_17;
 signed long int stepLocal_0 = last_1_var_1_17;
 if (var_1_2) {
  if (stepLocal_1 && var_1_5) {
   if (last_1_var_1_12 >= stepLocal_0) {
    var_1_1 = 5;
   } else {
    var_1_1 = ((((25) < (last_1_var_1_17)) ? (25) : (last_1_var_1_17)));
   }
  }
 } else {
  var_1_1 = last_1_var_1_17;
 }
 if (var_1_2) {
  var_1_7 = (((var_1_8 + var_1_9) + var_1_10) - var_1_11);
 }
 var_1_15 = var_1_8;
 var_1_16 = var_1_14;
 var_1_17 = var_1_18;
 signed long int stepLocal_3 = ((((-4 >> var_1_1)) < (var_1_1)) ? ((-4 >> var_1_1)) : (var_1_1));
 signed long int stepLocal_2 = var_1_1 / -8;
 if ((~ var_1_17) <= stepLocal_3) {
  if ((var_1_14 - 64) < stepLocal_2) {
   var_1_12 = var_1_1;
  }
 } else {
  var_1_12 = (var_1_17 - var_1_14);
 }
}
void updateVariables() {
 var_1_2 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_2 >= 0);
 assume_abort_if_not(var_1_2 <= 1);
 var_1_5 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_5 >= 0);
 assume_abort_if_not(var_1_5 <= 1);
 var_1_8 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_8 >= 0);
 assume_abort_if_not(var_1_8 <= 2147483647);
 var_1_9 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_9 >= 0);
 assume_abort_if_not(var_1_9 <= 2147483647);
 var_1_10 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_10 >= 0);
 assume_abort_if_not(var_1_10 <= 2147483647);
 var_1_11 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_11 >= 0);
 assume_abort_if_not(var_1_11 <= 2147483647);
 var_1_14 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_14 >= 127);
 assume_abort_if_not(var_1_14 <= 255);
 var_1_18 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_18 >= 0);
 assume_abort_if_not(var_1_18 <= 254);
}
void updateLastVariables() {
 last_1_var_1_12 = var_1_12;
 last_1_var_1_17 = var_1_17;
}
int property() {
 return (((((var_1_2 ? (((last_1_var_1_12 >= last_1_var_1_17) && var_1_5) ? ((last_1_var_1_12 >= last_1_var_1_17) ? (var_1_1 == ((unsigned short int) 5)) : (var_1_1 == ((unsigned short int) ((((25) < (last_1_var_1_17)) ? (25) : (last_1_var_1_17)))))) : 1) : (var_1_1 == ((unsigned short int) last_1_var_1_17))) && (var_1_2 ? (var_1_7 == ((signed long int) (((var_1_8 + var_1_9) + var_1_10) - var_1_11))) : 1)) && (((~ var_1_17) <= (((((-4 >> var_1_1)) < (var_1_1)) ? ((-4 >> var_1_1)) : (var_1_1)))) ? (((var_1_14 - 64) < (var_1_1 / -8)) ? (var_1_12 == ((signed long int) var_1_1)) : 1) : (var_1_12 == ((signed long int) (var_1_17 - var_1_14))))) && (var_1_15 == ((signed long int) var_1_8))) && (var_1_16 == ((unsigned long int) var_1_14))) && (var_1_17 == ((unsigned char) var_1_18))
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
