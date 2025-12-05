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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch51Amount10.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
signed short int var_1_1 = 25;
signed short int var_1_3 = 64;
signed short int var_1_4 = 50;
signed char var_1_7 = 0;
void initially(void) {
}
void step(void) {
 var_1_7 = 25;
 signed long int stepLocal_0 = -8;
 if (var_1_7 < stepLocal_0) {
  var_1_1 = (var_1_3 - var_1_4);
 } else {
  var_1_1 = ((((((((((((var_1_3) > (var_1_4)) ? (var_1_3) : (var_1_4)))) > ((var_1_7 + var_1_7))) ? (((((var_1_3) > (var_1_4)) ? (var_1_3) : (var_1_4)))) : ((var_1_7 + var_1_7))))) < (var_1_7)) ? (((((((((var_1_3) > (var_1_4)) ? (var_1_3) : (var_1_4)))) > ((var_1_7 + var_1_7))) ? (((((var_1_3) > (var_1_4)) ? (var_1_3) : (var_1_4)))) : ((var_1_7 + var_1_7))))) : (var_1_7)));
 }
}
void updateVariables() {
 var_1_3 = __VERIFIER_nondet_short();
 assume_abort_if_not(var_1_3 >= -1);
 assume_abort_if_not(var_1_3 <= 32766);
 var_1_4 = __VERIFIER_nondet_short();
 assume_abort_if_not(var_1_4 >= 0);
 assume_abort_if_not(var_1_4 <= 32766);
}
void updateLastVariables() {
}
int property() {
 return ((var_1_7 < -8) ? (var_1_1 == ((signed short int) (var_1_3 - var_1_4))) : (var_1_1 == ((signed short int) ((((((((((((var_1_3) > (var_1_4)) ? (var_1_3) : (var_1_4)))) > ((var_1_7 + var_1_7))) ? (((((var_1_3) > (var_1_4)) ? (var_1_3) : (var_1_4)))) : ((var_1_7 + var_1_7))))) < (var_1_7)) ? (((((((((var_1_3) > (var_1_4)) ? (var_1_3) : (var_1_4)))) > ((var_1_7 + var_1_7))) ? (((((var_1_3) > (var_1_4)) ? (var_1_3) : (var_1_4)))) : ((var_1_7 + var_1_7))))) : (var_1_7)))))) && (var_1_7 == ((signed char) 25))
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
