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
void reach_error() { __assert_fail("0", "Req1_Prop1_Batch1425_1loop.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
unsigned char isInitial = 0;
signed long int var_1_1 = 1000000;
unsigned char var_1_2 = 0;
signed short int var_1_5 = -64;
signed short int var_1_7 = 10;
signed short int var_1_8 = 8;
unsigned char var_1_9 = 0;
unsigned char var_1_10 = 0;
unsigned long int var_1_11 = 5;
signed char var_1_12 = 8;
signed char var_1_14 = 1;
signed char var_1_15 = 100;
signed char var_1_16 = 64;
signed char var_1_17 = 16;
signed long int var_1_18 = -256;
signed short int last_1_var_1_5 = -64;
unsigned char last_1_var_1_9 = 0;
signed char last_1_var_1_12 = 8;
void initially(void) {
}
void step(void) {
 if (last_1_var_1_9) {
  var_1_5 = last_1_var_1_12;
 } else {
  var_1_5 = ((var_1_7 + 16) - var_1_8);
 }
 signed long int stepLocal_1 = last_1_var_1_12 * last_1_var_1_5;
 if (var_1_8 <= stepLocal_1) {
  if (var_1_2) {
   var_1_9 = var_1_10;
  }
 }
 var_1_11 = ((((var_1_8) < (var_1_7)) ? (var_1_8) : (var_1_7)));
 var_1_18 = 256;
 unsigned char stepLocal_0 = var_1_9;
 if (var_1_9 && stepLocal_0) {
  var_1_1 = var_1_5;
 }
 signed long int stepLocal_2 = var_1_1;
 if (var_1_18 != stepLocal_2) {
  var_1_12 = (var_1_14 - ((((var_1_15) > (var_1_16)) ? (var_1_15) : (var_1_16))));
 } else {
  var_1_12 = (var_1_15 - ((var_1_17 + 5) + 10));
 }
}
void updateVariables() {
 var_1_2 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_2 >= 0);
 assume_abort_if_not(var_1_2 <= 1);
 var_1_7 = __VERIFIER_nondet_short();
 assume_abort_if_not(var_1_7 >= 0);
 assume_abort_if_not(var_1_7 <= 16383);
 var_1_8 = __VERIFIER_nondet_short();
 assume_abort_if_not(var_1_8 >= 0);
 assume_abort_if_not(var_1_8 <= 32766);
 var_1_10 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_10 >= 0);
 assume_abort_if_not(var_1_10 <= 0);
 var_1_14 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_14 >= -1);
 assume_abort_if_not(var_1_14 <= 126);
 var_1_15 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_15 >= 0);
 assume_abort_if_not(var_1_15 <= 126);
 var_1_16 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_16 >= 0);
 assume_abort_if_not(var_1_16 <= 126);
 var_1_17 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_17 >= 0);
 assume_abort_if_not(var_1_17 <= 32);
}
void updateLastVariables() {
 last_1_var_1_5 = var_1_5;
 last_1_var_1_9 = var_1_9;
 last_1_var_1_12 = var_1_12;
}
int property() {
 return ((((((var_1_9 && var_1_9) ? (var_1_1 == ((signed long int) var_1_5)) : 1) && (last_1_var_1_9 ? (var_1_5 == ((signed short int) last_1_var_1_12)) : (var_1_5 == ((signed short int) ((var_1_7 + 16) - var_1_8))))) && ((var_1_8 <= (last_1_var_1_12 * last_1_var_1_5)) ? (var_1_2 ? (var_1_9 == ((unsigned char) var_1_10)) : 1) : 1)) && (var_1_11 == ((unsigned long int) ((((var_1_8) < (var_1_7)) ? (var_1_8) : (var_1_7)))))) && ((var_1_18 != var_1_1) ? (var_1_12 == ((signed char) (var_1_14 - ((((var_1_15) > (var_1_16)) ? (var_1_15) : (var_1_16)))))) : (var_1_12 == ((signed char) (var_1_15 - ((var_1_17 + 5) + 10)))))) && (var_1_18 == ((signed long int) 256))
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
