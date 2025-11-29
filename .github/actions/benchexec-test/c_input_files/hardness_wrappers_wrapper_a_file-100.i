// This file is part of the SV-Benchmarks collection of verification tasks:
// https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks
//
// SPDX-FileCopyrightText: 2025 Jana Berger
//
// SPDX-License-Identifier: GPL-3.0-or-later

extern unsigned long __VERIFIER_nondet_ulong(void);
extern long __VERIFIER_nondet_long(void);
extern unsigned char __VERIFIER_nondet_uchar(void);
extern char __VERIFIER_nondet_char(void);
extern unsigned short __VERIFIER_nondet_ushort(void);
extern short __VERIFIER_nondet_short(void);
extern float __VERIFIER_nondet_float(void);
extern double __VERIFIER_nondet_double(void);
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error(void) { __assert_fail("0", "Req1_Prop1_Batch100Wrapper_A.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
void initially(void);
void step(void);
void updateVariables(void);
void updateLastVariables(void);
int property(void);
int main(void);
unsigned char isInitial = 0;
unsigned char BOOL_unsigned_char_Array_0[5] = {
 0, 0, 0, 1, 1
};
signed short int signed_short_int_Array_0[2][3] = {
 {10000, -128, 50}, {200, 1, 100}
};
unsigned char unsigned_char_Array_0[3] = {
 128, 128, 64
};
unsigned long int unsigned_long_int_Array_0[2][2][2] = {
 {{25, 50}, {1401937267, 16}}, {{1707018182, 10000}, {1438530836, 8}}
};
unsigned char last_1_BOOL_unsigned_char_Array_0_0_ = 0;
void initially(void) {
}
void step(void) {
 unsigned char stepLocal_0 = last_1_BOOL_unsigned_char_Array_0_0_;
 if ((unsigned_long_int_Array_0[0][1][1] >= unsigned_long_int_Array_0[1][0][1]) || stepLocal_0) {
  unsigned_long_int_Array_0[1][1][1] = ((((((((unsigned_long_int_Array_0[0][0][1]) < (32u)) ? (unsigned_long_int_Array_0[0][0][1]) : (32u)))) < (((unsigned_long_int_Array_0[1][1][0] + unsigned_long_int_Array_0[0][1][0]) - (unsigned_long_int_Array_0[1][0][0] - unsigned_long_int_Array_0[0][0][0])))) ? (((((unsigned_long_int_Array_0[0][0][1]) < (32u)) ? (unsigned_long_int_Array_0[0][0][1]) : (32u)))) : (((unsigned_long_int_Array_0[1][1][0] + unsigned_long_int_Array_0[0][1][0]) - (unsigned_long_int_Array_0[1][0][0] - unsigned_long_int_Array_0[0][0][0])))));
 } else {
  unsigned_long_int_Array_0[1][1][1] = unsigned_long_int_Array_0[0][0][0];
 }
 signed long int stepLocal_2 = 1000;
 if (signed_short_int_Array_0[1][0] < stepLocal_2) {
  BOOL_unsigned_char_Array_0[0] = (BOOL_unsigned_char_Array_0[3] && ((unsigned_long_int_Array_0[1][1][1] > 64u) || BOOL_unsigned_char_Array_0[4]));
 } else {
  BOOL_unsigned_char_Array_0[0] = (! (BOOL_unsigned_char_Array_0[1] || BOOL_unsigned_char_Array_0[2]));
 }
 signed_short_int_Array_0[0][1] = (signed_short_int_Array_0[1][1] - ((signed_short_int_Array_0[0][0] - signed_short_int_Array_0[1][0]) + ((((signed_short_int_Array_0[0][2]) < (signed_short_int_Array_0[1][2])) ? (signed_short_int_Array_0[0][2]) : (signed_short_int_Array_0[1][2])))));
 signed long int stepLocal_1 = signed_short_int_Array_0[0][2] % signed_short_int_Array_0[0][0];
 if (stepLocal_1 <= unsigned_long_int_Array_0[1][1][1]) {
  unsigned_char_Array_0[0] = ((((((((unsigned_char_Array_0[1]) > (128)) ? (unsigned_char_Array_0[1]) : (128)))) < (unsigned_char_Array_0[2])) ? (((((unsigned_char_Array_0[1]) > (128)) ? (unsigned_char_Array_0[1]) : (128)))) : (unsigned_char_Array_0[2])));
 }
}
void updateVariables(void) {
 BOOL_unsigned_char_Array_0[1] = __VERIFIER_nondet_uchar();
 assume_abort_if_not(BOOL_unsigned_char_Array_0[1] >= 0);
 assume_abort_if_not(BOOL_unsigned_char_Array_0[1] <= 0);
 BOOL_unsigned_char_Array_0[2] = __VERIFIER_nondet_uchar();
 assume_abort_if_not(BOOL_unsigned_char_Array_0[2] >= 0);
 assume_abort_if_not(BOOL_unsigned_char_Array_0[2] <= 0);
 BOOL_unsigned_char_Array_0[3] = __VERIFIER_nondet_uchar();
 assume_abort_if_not(BOOL_unsigned_char_Array_0[3] >= 1);
 assume_abort_if_not(BOOL_unsigned_char_Array_0[3] <= 1);
 BOOL_unsigned_char_Array_0[4] = __VERIFIER_nondet_uchar();
 assume_abort_if_not(BOOL_unsigned_char_Array_0[4] >= 1);
 assume_abort_if_not(BOOL_unsigned_char_Array_0[4] <= 1);
 signed_short_int_Array_0[0][0] = __VERIFIER_nondet_short();
 assume_abort_if_not(signed_short_int_Array_0[0][0] >= 8191);
 assume_abort_if_not(signed_short_int_Array_0[0][0] <= 16383);
 signed_short_int_Array_0[1][0] = __VERIFIER_nondet_short();
 assume_abort_if_not(signed_short_int_Array_0[1][0] >= 0);
 assume_abort_if_not(signed_short_int_Array_0[1][0] <= 8191);
 signed_short_int_Array_0[1][1] = __VERIFIER_nondet_short();
 assume_abort_if_not(signed_short_int_Array_0[1][1] >= -1);
 assume_abort_if_not(signed_short_int_Array_0[1][1] <= 32766);
 signed_short_int_Array_0[0][2] = __VERIFIER_nondet_short();
 assume_abort_if_not(signed_short_int_Array_0[0][2] >= 0);
 assume_abort_if_not(signed_short_int_Array_0[0][2] <= 16383);
 signed_short_int_Array_0[1][2] = __VERIFIER_nondet_short();
 assume_abort_if_not(signed_short_int_Array_0[1][2] >= 0);
 assume_abort_if_not(signed_short_int_Array_0[1][2] <= 16383);
 unsigned_char_Array_0[1] = __VERIFIER_nondet_uchar();
 assume_abort_if_not(unsigned_char_Array_0[1] >= 0);
 assume_abort_if_not(unsigned_char_Array_0[1] <= 254);
 unsigned_char_Array_0[2] = __VERIFIER_nondet_uchar();
 assume_abort_if_not(unsigned_char_Array_0[2] >= 0);
 assume_abort_if_not(unsigned_char_Array_0[2] <= 254);
 unsigned_long_int_Array_0[0][0][0] = __VERIFIER_nondet_ulong();
 assume_abort_if_not(unsigned_long_int_Array_0[0][0][0] >= 0);
 assume_abort_if_not(unsigned_long_int_Array_0[0][0][0] <= 1073741823);
 unsigned_long_int_Array_0[1][0][0] = __VERIFIER_nondet_ulong();
 assume_abort_if_not(unsigned_long_int_Array_0[1][0][0] >= 1073741823);
 assume_abort_if_not(unsigned_long_int_Array_0[1][0][0] <= 2147483647);
 unsigned_long_int_Array_0[0][1][0] = __VERIFIER_nondet_ulong();
 assume_abort_if_not(unsigned_long_int_Array_0[0][1][0] >= 1073741824);
 assume_abort_if_not(unsigned_long_int_Array_0[0][1][0] <= 2147483647);
 unsigned_long_int_Array_0[1][1][0] = __VERIFIER_nondet_ulong();
 assume_abort_if_not(unsigned_long_int_Array_0[1][1][0] >= 1073741823);
 assume_abort_if_not(unsigned_long_int_Array_0[1][1][0] <= 2147483647);
 unsigned_long_int_Array_0[0][0][1] = __VERIFIER_nondet_ulong();
 assume_abort_if_not(unsigned_long_int_Array_0[0][0][1] >= 0);
 assume_abort_if_not(unsigned_long_int_Array_0[0][0][1] <= 4294967294);
 unsigned_long_int_Array_0[1][0][1] = __VERIFIER_nondet_ulong();
 assume_abort_if_not(unsigned_long_int_Array_0[1][0][1] >= 0);
 assume_abort_if_not(unsigned_long_int_Array_0[1][0][1] <= 4294967295);
 unsigned_long_int_Array_0[0][1][1] = __VERIFIER_nondet_ulong();
 assume_abort_if_not(unsigned_long_int_Array_0[0][1][1] >= 0);
 assume_abort_if_not(unsigned_long_int_Array_0[0][1][1] <= 4294967295);
}
void updateLastVariables(void) {
 last_1_BOOL_unsigned_char_Array_0_0_ = BOOL_unsigned_char_Array_0[0];
}
int property(void) {
 return (((((unsigned_long_int_Array_0[0][1][1] >= unsigned_long_int_Array_0[1][0][1]) || last_1_BOOL_unsigned_char_Array_0_0_) ? (unsigned_long_int_Array_0[1][1][1] == ((unsigned long int) ((((((((unsigned_long_int_Array_0[0][0][1]) < (32u)) ? (unsigned_long_int_Array_0[0][0][1]) : (32u)))) < (((unsigned_long_int_Array_0[1][1][0] + unsigned_long_int_Array_0[0][1][0]) - (unsigned_long_int_Array_0[1][0][0] - unsigned_long_int_Array_0[0][0][0])))) ? (((((unsigned_long_int_Array_0[0][0][1]) < (32u)) ? (unsigned_long_int_Array_0[0][0][1]) : (32u)))) : (((unsigned_long_int_Array_0[1][1][0] + unsigned_long_int_Array_0[0][1][0]) - (unsigned_long_int_Array_0[1][0][0] - unsigned_long_int_Array_0[0][0][0]))))))) : (unsigned_long_int_Array_0[1][1][1] == ((unsigned long int) unsigned_long_int_Array_0[0][0][0]))) && (signed_short_int_Array_0[0][1] == ((signed short int) (signed_short_int_Array_0[1][1] - ((signed_short_int_Array_0[0][0] - signed_short_int_Array_0[1][0]) + ((((signed_short_int_Array_0[0][2]) < (signed_short_int_Array_0[1][2])) ? (signed_short_int_Array_0[0][2]) : (signed_short_int_Array_0[1][2])))))))) && (((signed_short_int_Array_0[0][2] % signed_short_int_Array_0[0][0]) <= unsigned_long_int_Array_0[1][1][1]) ? (unsigned_char_Array_0[0] == ((unsigned char) ((((((((unsigned_char_Array_0[1]) > (128)) ? (unsigned_char_Array_0[1]) : (128)))) < (unsigned_char_Array_0[2])) ? (((((unsigned_char_Array_0[1]) > (128)) ? (unsigned_char_Array_0[1]) : (128)))) : (unsigned_char_Array_0[2]))))) : 1)) && ((signed_short_int_Array_0[1][0] < 1000) ? (BOOL_unsigned_char_Array_0[0] == ((unsigned char) (BOOL_unsigned_char_Array_0[3] && ((unsigned_long_int_Array_0[1][1][1] > 64u) || BOOL_unsigned_char_Array_0[4])))) : (BOOL_unsigned_char_Array_0[0] == ((unsigned char) (! (BOOL_unsigned_char_Array_0[1] || BOOL_unsigned_char_Array_0[2])))))
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
