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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch1325_1loop.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
unsigned short int var_1_1 = 25;
signed char var_1_5 = 16;
signed char var_1_6 = -5;
unsigned short int var_1_7 = 100;
unsigned short int var_1_8 = 44038;
signed long int var_1_10 = 256;
unsigned char var_1_11 = 5;
unsigned char var_1_12 = 16;
unsigned char var_1_13 = 64;
unsigned char var_1_14 = 128;
unsigned char var_1_15 = 4;
unsigned char var_1_16 = 1;
unsigned char var_1_17 = 16;
unsigned char var_1_18 = 1;
signed long int var_1_19 = -16;
unsigned short int var_1_20 = 0;
void initially(void) {
}
void step(void) {
 var_1_18 = 0;
 var_1_20 = var_1_15;
 if (! var_1_18) {
  var_1_11 = (var_1_12 + var_1_13);
 } else {
  var_1_11 = (((((((((var_1_14 - var_1_13)) > (var_1_12)) ? ((var_1_14 - var_1_13)) : (var_1_12)))) > (((var_1_15 + var_1_16) + var_1_17))) ? ((((((var_1_14 - var_1_13)) > (var_1_12)) ? ((var_1_14 - var_1_13)) : (var_1_12)))) : (((var_1_15 + var_1_16) + var_1_17))));
 }
 if (var_1_18) {
  var_1_1 = ((((var_1_11) > (var_1_11)) ? (var_1_11) : (var_1_11)));
 }
 if ((var_1_1 == 16) || (var_1_11 < var_1_11)) {
  var_1_5 = var_1_6;
 }
 var_1_7 = (var_1_8 - var_1_11);
 var_1_10 = ((((var_1_11) < (var_1_6)) ? (var_1_11) : (var_1_6)));
 var_1_19 = var_1_1;
}
void updateVariables() {
 var_1_6 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_6 >= -127);
 assume_abort_if_not(var_1_6 <= 126);
 var_1_8 = __VERIFIER_nondet_ushort();
 assume_abort_if_not(var_1_8 >= 32767);
 assume_abort_if_not(var_1_8 <= 65534);
 var_1_12 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_12 >= 0);
 assume_abort_if_not(var_1_12 <= 127);
 var_1_13 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_13 >= 0);
 assume_abort_if_not(var_1_13 <= 127);
 var_1_14 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_14 >= 127);
 assume_abort_if_not(var_1_14 <= 254);
 var_1_15 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_15 >= 0);
 assume_abort_if_not(var_1_15 <= 64);
 var_1_16 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_16 >= 0);
 assume_abort_if_not(var_1_16 <= 63);
 var_1_17 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_17 >= 0);
 assume_abort_if_not(var_1_17 <= 127);
}
void updateLastVariables() {
}
int property() {
 return (((((((var_1_18 ? (var_1_1 == ((unsigned short int) ((((var_1_11) > (var_1_11)) ? (var_1_11) : (var_1_11))))) : 1) && (((var_1_1 == 16) || (var_1_11 < var_1_11)) ? (var_1_5 == ((signed char) var_1_6)) : 1)) && (var_1_7 == ((unsigned short int) (var_1_8 - var_1_11)))) && (var_1_10 == ((signed long int) ((((var_1_11) < (var_1_6)) ? (var_1_11) : (var_1_6)))))) && ((! var_1_18) ? (var_1_11 == ((unsigned char) (var_1_12 + var_1_13))) : (var_1_11 == ((unsigned char) (((((((((var_1_14 - var_1_13)) > (var_1_12)) ? ((var_1_14 - var_1_13)) : (var_1_12)))) > (((var_1_15 + var_1_16) + var_1_17))) ? ((((((var_1_14 - var_1_13)) > (var_1_12)) ? ((var_1_14 - var_1_13)) : (var_1_12)))) : (((var_1_15 + var_1_16) + var_1_17)))))))) && (var_1_18 == ((unsigned char) 0))) && (var_1_19 == ((signed long int) var_1_1))) && (var_1_20 == ((unsigned short int) var_1_15))
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
