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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch82Amount10.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
unsigned char var_1_1 = 64;
unsigned short int var_1_3 = 8;
unsigned short int var_1_4 = 4;
unsigned short int var_1_5 = 5;
unsigned char var_1_6 = 64;
unsigned char var_1_7 = 4;
unsigned char var_1_8 = 1;
unsigned char last_1_var_1_1 = 64;
void initially(void) {
}
void step(void) {
 if (last_1_var_1_1 >= (var_1_3 + (var_1_4 + var_1_5))) {
  var_1_1 = ((((var_1_6) < (var_1_7)) ? (var_1_6) : (var_1_7)));
 } else {
  if (last_1_var_1_1 > var_1_6) {
   if (var_1_8) {
    var_1_1 = var_1_6;
   } else {
    var_1_1 = var_1_7;
   }
  } else {
   var_1_1 = var_1_6;
  }
 }
}
void updateVariables() {
 var_1_3 = __VERIFIER_nondet_ushort();
 assume_abort_if_not(var_1_3 >= 0);
 assume_abort_if_not(var_1_3 <= 65535);
 var_1_4 = __VERIFIER_nondet_ushort();
 assume_abort_if_not(var_1_4 >= 0);
 assume_abort_if_not(var_1_4 <= 65535);
 var_1_5 = __VERIFIER_nondet_ushort();
 assume_abort_if_not(var_1_5 >= 0);
 assume_abort_if_not(var_1_5 <= 65535);
 var_1_6 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_6 >= 0);
 assume_abort_if_not(var_1_6 <= 254);
 var_1_7 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_7 >= 0);
 assume_abort_if_not(var_1_7 <= 254);
 var_1_8 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_8 >= 0);
 assume_abort_if_not(var_1_8 <= 1);
}
void updateLastVariables() {
 last_1_var_1_1 = var_1_1;
}
int property() {
 return (last_1_var_1_1 >= (var_1_3 + (var_1_4 + var_1_5))) ? (var_1_1 == ((unsigned char) ((((var_1_6) < (var_1_7)) ? (var_1_6) : (var_1_7))))) : ((last_1_var_1_1 > var_1_6) ? (var_1_8 ? (var_1_1 == ((unsigned char) var_1_6)) : (var_1_1 == ((unsigned char) var_1_7))) : (var_1_1 == ((unsigned char) var_1_6)))
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
