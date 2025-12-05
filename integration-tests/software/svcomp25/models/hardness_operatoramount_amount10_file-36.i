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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch36Amount10.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
unsigned char var_1_1 = 1;
signed long int var_1_2 = 1657634462;
signed long int var_1_3 = 8;
signed long int var_1_4 = 16;
signed long int var_1_5 = 0;
unsigned char var_1_6 = 0;
signed char var_1_7 = 2;
signed char var_1_8 = -16;
signed char last_1_var_1_7 = 2;
void initially(void) {
}
void step(void) {
 signed long int stepLocal_0 = (var_1_2 - var_1_3) - var_1_4;
 if (stepLocal_0 <= last_1_var_1_7) {
  var_1_1 = (! var_1_6);
 }
 signed long int stepLocal_1 = var_1_5;
 if (stepLocal_1 >= var_1_3) {
  if (var_1_6) {
   if (var_1_1) {
    var_1_7 = var_1_8;
   }
  }
 }
}
void updateVariables() {
 var_1_2 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_2 >= 1073741823);
 assume_abort_if_not(var_1_2 <= 2147483647);
 var_1_3 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_3 >= 0);
 assume_abort_if_not(var_1_3 <= 1073741824);
 var_1_4 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_4 >= 0);
 assume_abort_if_not(var_1_4 <= 2147483647);
 var_1_5 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_5 >= -2147483648);
 assume_abort_if_not(var_1_5 <= 2147483647);
 var_1_6 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_6 >= 0);
 assume_abort_if_not(var_1_6 <= 0);
 var_1_8 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_8 >= -127);
 assume_abort_if_not(var_1_8 <= 126);
}
void updateLastVariables() {
 last_1_var_1_7 = var_1_7;
}
int property() {
 return ((((var_1_2 - var_1_3) - var_1_4) <= last_1_var_1_7) ? (var_1_1 == ((unsigned char) (! var_1_6))) : 1) && ((var_1_5 >= var_1_3) ? (var_1_6 ? (var_1_1 ? (var_1_7 == ((signed char) var_1_8)) : 1) : 1) : 1)
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
