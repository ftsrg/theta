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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch12Amount10.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
signed char var_1_1 = 4;
signed char var_1_4 = -1;
signed char var_1_5 = 100;
signed long int var_1_6 = 1000;
double var_1_7 = 4.5;
unsigned char var_1_8 = 1;
unsigned char var_1_9 = 0;
signed long int var_1_10 = 256;
signed char last_1_var_1_1 = 4;
void initially(void) {
}
void step(void) {
 var_1_7 = 199.5;
 var_1_8 = var_1_9;
 var_1_10 = var_1_5;
 signed long int stepLocal_0 = var_1_10;
 if (stepLocal_0 >= last_1_var_1_1) {
  var_1_1 = (((((((var_1_4) < (var_1_5)) ? (var_1_4) : (var_1_5))) < 0 ) ? -((((var_1_4) < (var_1_5)) ? (var_1_4) : (var_1_5))) : ((((var_1_4) < (var_1_5)) ? (var_1_4) : (var_1_5)))));
 }
 var_1_6 = ((((var_1_4) > (var_1_1)) ? (var_1_4) : (var_1_1)));
}
void updateVariables() {
 var_1_4 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_4 >= -126);
 assume_abort_if_not(var_1_4 <= 126);
 var_1_5 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_5 >= -126);
 assume_abort_if_not(var_1_5 <= 126);
 var_1_9 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_9 >= 0);
 assume_abort_if_not(var_1_9 <= 0);
}
void updateLastVariables() {
 last_1_var_1_1 = var_1_1;
}
int property() {
 return (((((var_1_10 >= last_1_var_1_1) ? (var_1_1 == ((signed char) (((((((var_1_4) < (var_1_5)) ? (var_1_4) : (var_1_5))) < 0 ) ? -((((var_1_4) < (var_1_5)) ? (var_1_4) : (var_1_5))) : ((((var_1_4) < (var_1_5)) ? (var_1_4) : (var_1_5))))))) : 1) && (var_1_6 == ((signed long int) ((((var_1_4) > (var_1_1)) ? (var_1_4) : (var_1_1)))))) && (var_1_7 == ((double) 199.5))) && (var_1_8 == ((unsigned char) var_1_9))) && (var_1_10 == ((signed long int) var_1_5))
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
