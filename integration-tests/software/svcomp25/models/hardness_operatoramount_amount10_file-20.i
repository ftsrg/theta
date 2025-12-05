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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch20Amount10.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
signed long int var_1_1 = 5;
unsigned char var_1_2 = 0;
signed long int var_1_3 = 256;
signed long int var_1_6 = 0;
unsigned char var_1_7 = 32;
unsigned char var_1_8 = 128;
unsigned char last_1_var_1_7 = 32;
void initially(void) {
}
void step(void) {
 if (var_1_2) {
  var_1_1 = last_1_var_1_7;
 } else {
  var_1_1 = ((((last_1_var_1_7) < (((((last_1_var_1_7) > (((((last_1_var_1_7) < (last_1_var_1_7)) ? (last_1_var_1_7) : (last_1_var_1_7))))) ? (last_1_var_1_7) : (((((last_1_var_1_7) < (last_1_var_1_7)) ? (last_1_var_1_7) : (last_1_var_1_7)))))))) ? (last_1_var_1_7) : (((((last_1_var_1_7) > (((((last_1_var_1_7) < (last_1_var_1_7)) ? (last_1_var_1_7) : (last_1_var_1_7))))) ? (last_1_var_1_7) : (((((last_1_var_1_7) < (last_1_var_1_7)) ? (last_1_var_1_7) : (last_1_var_1_7)))))))));
 }
 if ((((((var_1_6) > (last_1_var_1_7)) ? (var_1_6) : (last_1_var_1_7))) + var_1_1) >= var_1_3) {
  var_1_7 = var_1_8;
 }
}
void updateVariables() {
 var_1_2 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_2 >= 0);
 assume_abort_if_not(var_1_2 <= 1);
 var_1_3 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_3 >= -2147483647);
 assume_abort_if_not(var_1_3 <= 2147483646);
 var_1_6 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_6 >= -2147483647);
 assume_abort_if_not(var_1_6 <= 2147483646);
 var_1_8 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_8 >= 0);
 assume_abort_if_not(var_1_8 <= 254);
}
void updateLastVariables() {
 last_1_var_1_7 = var_1_7;
}
int property() {
 return (var_1_2 ? (var_1_1 == ((signed long int) last_1_var_1_7)) : (var_1_1 == ((signed long int) ((((last_1_var_1_7) < (((((last_1_var_1_7) > (((((last_1_var_1_7) < (last_1_var_1_7)) ? (last_1_var_1_7) : (last_1_var_1_7))))) ? (last_1_var_1_7) : (((((last_1_var_1_7) < (last_1_var_1_7)) ? (last_1_var_1_7) : (last_1_var_1_7)))))))) ? (last_1_var_1_7) : (((((last_1_var_1_7) > (((((last_1_var_1_7) < (last_1_var_1_7)) ? (last_1_var_1_7) : (last_1_var_1_7))))) ? (last_1_var_1_7) : (((((last_1_var_1_7) < (last_1_var_1_7)) ? (last_1_var_1_7) : (last_1_var_1_7)))))))))))) && (((((((var_1_6) > (last_1_var_1_7)) ? (var_1_6) : (last_1_var_1_7))) + var_1_1) >= var_1_3) ? (var_1_7 == ((unsigned char) var_1_8)) : 1)
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
