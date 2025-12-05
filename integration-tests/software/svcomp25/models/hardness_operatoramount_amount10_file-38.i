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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch38Amount10.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
float var_1_1 = 256.2;
unsigned char var_1_2 = 0;
unsigned char var_1_3 = 0;
unsigned short int var_1_5 = 0;
float var_1_6 = 10.125;
float var_1_7 = 9.4;
unsigned long int var_1_8 = 50;
void initially(void) {
}
void step(void) {
 var_1_8 = var_1_5;
 if (var_1_2 || var_1_3) {
  if (var_1_8 != var_1_8) {
   var_1_1 = ((((-0.4f) > (((((var_1_6 + var_1_7) < 0 ) ? -(var_1_6 + var_1_7) : (var_1_6 + var_1_7))))) ? (-0.4f) : (((((var_1_6 + var_1_7) < 0 ) ? -(var_1_6 + var_1_7) : (var_1_6 + var_1_7))))));
  } else {
   var_1_1 = var_1_6;
  }
 }
}
void updateVariables() {
 var_1_2 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_2 >= 0);
 assume_abort_if_not(var_1_2 <= 1);
 var_1_3 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_3 >= 0);
 assume_abort_if_not(var_1_3 <= 1);
 var_1_5 = __VERIFIER_nondet_ushort();
 assume_abort_if_not(var_1_5 >= 0);
 assume_abort_if_not(var_1_5 <= 65535);
 var_1_6 = __VERIFIER_nondet_float();
 assume_abort_if_not((var_1_6 >= -461168.6018427382800e+13F && var_1_6 <= -1.0e-20F) || (var_1_6 <= 4611686.018427382800e+12F && var_1_6 >= 1.0e-20F ));
 var_1_7 = __VERIFIER_nondet_float();
 assume_abort_if_not((var_1_7 >= -461168.6018427382800e+13F && var_1_7 <= -1.0e-20F) || (var_1_7 <= 4611686.018427382800e+12F && var_1_7 >= 1.0e-20F ));
}
void updateLastVariables() {
}
int property() {
 return ((var_1_2 || var_1_3) ? ((var_1_8 != var_1_8) ? (var_1_1 == ((float) ((((-0.4f) > (((((var_1_6 + var_1_7) < 0 ) ? -(var_1_6 + var_1_7) : (var_1_6 + var_1_7))))) ? (-0.4f) : (((((var_1_6 + var_1_7) < 0 ) ? -(var_1_6 + var_1_7) : (var_1_6 + var_1_7)))))))) : (var_1_1 == ((float) var_1_6))) : 1) && (var_1_8 == ((unsigned long int) var_1_5))
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
