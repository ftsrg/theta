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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch4925_while.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
unsigned short int var_1_1 = 4;
float var_1_2 = 1000000000000000.4;
float var_1_3 = 1000.2;
unsigned short int var_1_4 = 256;
unsigned short int var_1_5 = 4;
unsigned short int var_1_6 = 10;
signed short int var_1_8 = 128;
unsigned char var_1_10 = 0;
unsigned char var_1_11 = 0;
unsigned char var_1_12 = 0;
unsigned char var_1_13 = 1;
unsigned char var_1_14 = 0;
signed char var_1_15 = -1;
signed char var_1_16 = 0;
void initially(void) {
}
void step(void) {
 var_1_13 = var_1_14;
 var_1_15 = var_1_16;
 if (var_1_2 >= 64.5f) {
  if (var_1_2 >= var_1_3) {
   var_1_1 = (((((((var_1_4) > (((((var_1_5) > (var_1_6)) ? (var_1_5) : (var_1_6))))) ? (var_1_4) : (((((var_1_5) > (var_1_6)) ? (var_1_5) : (var_1_6)))))) < 0 ) ? -((((var_1_4) > (((((var_1_5) > (var_1_6)) ? (var_1_5) : (var_1_6))))) ? (var_1_4) : (((((var_1_5) > (var_1_6)) ? (var_1_5) : (var_1_6)))))) : ((((var_1_4) > (((((var_1_5) > (var_1_6)) ? (var_1_5) : (var_1_6))))) ? (var_1_4) : (((((var_1_5) > (var_1_6)) ? (var_1_5) : (var_1_6))))))));
  } else {
   if (var_1_13) {
    var_1_1 = var_1_5;
   } else {
    var_1_1 = var_1_6;
   }
  }
 } else {
  var_1_1 = 50;
 }
 var_1_8 = ((((var_1_15) < 0 ) ? -(var_1_15) : (var_1_15)));
 if ((50 >> var_1_4) <= var_1_8) {
  var_1_10 = ((! (! var_1_11)) || var_1_12);
 } else {
  var_1_10 = (! var_1_11);
 }
}
void updateVariables() {
 var_1_2 = __VERIFIER_nondet_float();
 assume_abort_if_not((var_1_2 >= -922337.2036854776000e+13F && var_1_2 <= -1.0e-20F) || (var_1_2 <= 9223372.036854776000e+12F && var_1_2 >= 1.0e-20F ));
 var_1_3 = __VERIFIER_nondet_float();
 assume_abort_if_not((var_1_3 >= -922337.2036854776000e+13F && var_1_3 <= -1.0e-20F) || (var_1_3 <= 9223372.036854776000e+12F && var_1_3 >= 1.0e-20F ));
 var_1_4 = __VERIFIER_nondet_ushort();
 assume_abort_if_not(var_1_4 >= 0);
 assume_abort_if_not(var_1_4 <= 65534);
 var_1_5 = __VERIFIER_nondet_ushort();
 assume_abort_if_not(var_1_5 >= 0);
 assume_abort_if_not(var_1_5 <= 65534);
 var_1_6 = __VERIFIER_nondet_ushort();
 assume_abort_if_not(var_1_6 >= 0);
 assume_abort_if_not(var_1_6 <= 65534);
 var_1_11 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_11 >= 0);
 assume_abort_if_not(var_1_11 <= 0);
 var_1_12 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_12 >= 0);
 assume_abort_if_not(var_1_12 <= 0);
 var_1_14 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_14 >= 1);
 assume_abort_if_not(var_1_14 <= 1);
 var_1_16 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_16 >= -127);
 assume_abort_if_not(var_1_16 <= 126);
}
void updateLastVariables() {
}
int property() {
 return (((((var_1_2 >= 64.5f) ? ((var_1_2 >= var_1_3) ? (var_1_1 == ((unsigned short int) (((((((var_1_4) > (((((var_1_5) > (var_1_6)) ? (var_1_5) : (var_1_6))))) ? (var_1_4) : (((((var_1_5) > (var_1_6)) ? (var_1_5) : (var_1_6)))))) < 0 ) ? -((((var_1_4) > (((((var_1_5) > (var_1_6)) ? (var_1_5) : (var_1_6))))) ? (var_1_4) : (((((var_1_5) > (var_1_6)) ? (var_1_5) : (var_1_6)))))) : ((((var_1_4) > (((((var_1_5) > (var_1_6)) ? (var_1_5) : (var_1_6))))) ? (var_1_4) : (((((var_1_5) > (var_1_6)) ? (var_1_5) : (var_1_6)))))))))) : (var_1_13 ? (var_1_1 == ((unsigned short int) var_1_5)) : (var_1_1 == ((unsigned short int) var_1_6)))) : (var_1_1 == ((unsigned short int) 50))) && (var_1_8 == ((signed short int) ((((var_1_15) < 0 ) ? -(var_1_15) : (var_1_15)))))) && (((50 >> var_1_4) <= var_1_8) ? (var_1_10 == ((unsigned char) ((! (! var_1_11)) || var_1_12))) : (var_1_10 == ((unsigned char) (! var_1_11))))) && (var_1_13 == ((unsigned char) var_1_14))) && (var_1_15 == ((signed char) var_1_16))
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
