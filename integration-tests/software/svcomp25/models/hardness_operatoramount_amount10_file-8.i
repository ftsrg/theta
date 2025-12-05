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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch8Amount10.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
unsigned short int var_1_1 = 128;
unsigned short int var_1_6 = 10;
unsigned short int var_1_7 = 50;
signed char var_1_8 = 0;
signed char var_1_9 = 64;
unsigned short int var_1_10 = 64;
signed long int var_1_11 = -8;
void initially(void) {
}
void step(void) {
 var_1_8 = var_1_9;
 var_1_10 = var_1_7;
 var_1_11 = -1;
 if (var_1_8 < (var_1_10 - (var_1_10 + var_1_10))) {
  var_1_1 = (38267 - (var_1_6 + var_1_7));
 }
}
void updateVariables() {
 var_1_6 = __VERIFIER_nondet_ushort();
 assume_abort_if_not(var_1_6 >= 0);
 assume_abort_if_not(var_1_6 <= 16384);
 var_1_7 = __VERIFIER_nondet_ushort();
 assume_abort_if_not(var_1_7 >= 0);
 assume_abort_if_not(var_1_7 <= 16383);
 var_1_9 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_9 >= -127);
 assume_abort_if_not(var_1_9 <= 126);
}
void updateLastVariables() {
}
int property() {
 return ((((var_1_8 < (var_1_10 - (var_1_10 + var_1_10))) ? (var_1_1 == ((unsigned short int) (38267 - (var_1_6 + var_1_7)))) : 1) && (var_1_8 == ((signed char) var_1_9))) && (var_1_10 == ((unsigned short int) var_1_7))) && (var_1_11 == ((signed long int) -1))
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
