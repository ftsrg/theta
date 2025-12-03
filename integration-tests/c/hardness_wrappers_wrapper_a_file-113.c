// This file is part of the SV-Benchmarks collection of verification tasks:
// https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks
//
// SPDX-FileCopyrightText: 2025 Jana Berger
//
// SPDX-License-Identifier: GPL-3.0-or-later

// Prototype declarations of the functions used to communicate with the model checkers
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
void reach_error(void) { __assert_fail("0", "Req1_Prop1_Batch113Wrapper_A.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }



#define max(a,b) (((a) > (b)) ? (a) : (b))
#define min(a,b) (((a) < (b)) ? (a) : (b))
#define abs(a) (((a) < 0 ) ? -(a) : (a))





// Function prototypes
void initially(void);
void step(void);
void updateVariables(void);
void updateLastVariables(void);
int property(void);
int main(void);


// Internal control logic variables
unsigned char isInitial = 0;

// Signal variables
unsigned char BOOL_unsigned_char_Array_0[2] = {
	0, 0
};
float float_Array_0[5] = {
	7.5, 64.25, 0.0, 10.6, 1.5
};
signed char signed_char_Array_0[2] = {
	2, -32
};
unsigned long int unsigned_long_int_Array_0[2][2] = {
	{256, 32}, {25, 5}
};
unsigned short int unsigned_short_int_Array_0[2][3] = {
	{18561, 64, 1}, {22430, 8, 2}
};

// Calibration values

// Last'ed variables

// Additional functions


void initially(void) {
}



void step(void) {
	// From: Req1Batch113Wrapper_A
	unsigned long int stepLocal_0 = unsigned_long_int_Array_0[0][1];
	if (unsigned_long_int_Array_0[1][1] >= stepLocal_0) {
		unsigned_short_int_Array_0[1][2] = (min (128 , unsigned_short_int_Array_0[0][2]));
	} else {
		unsigned_short_int_Array_0[1][2] = (min ((unsigned_short_int_Array_0[1][1] + unsigned_short_int_Array_0[0][1]) , unsigned_short_int_Array_0[0][2]));
	}


	// From: Req4Batch113Wrapper_A
	if (BOOL_unsigned_char_Array_0[0] && BOOL_unsigned_char_Array_0[1]) {
		if (float_Array_0[0] > ((float_Array_0[2] - float_Array_0[3]) - float_Array_0[4])) {
			unsigned_long_int_Array_0[0][0] = unsigned_long_int_Array_0[1][0];
		}
	} else {
		unsigned_long_int_Array_0[0][0] = unsigned_short_int_Array_0[0][1];
	}


	// From: Req2Batch113Wrapper_A
	if (unsigned_long_int_Array_0[0][0] >= unsigned_short_int_Array_0[0][1]) {
		float_Array_0[1] = float_Array_0[0];
	}


	// From: Req3Batch113Wrapper_A
	if (-64 >= unsigned_long_int_Array_0[0][0]) {
		if ((-1000 < 256) && ((max (unsigned_long_int_Array_0[0][0] , unsigned_short_int_Array_0[0][1])) > unsigned_short_int_Array_0[0][2])) {
			if (unsigned_short_int_Array_0[0][2] < ((unsigned_short_int_Array_0[1][0] + unsigned_short_int_Array_0[0][0]) - unsigned_short_int_Array_0[0][1])) {
				signed_char_Array_0[0] = signed_char_Array_0[1];
			}
		} else {
			signed_char_Array_0[0] = signed_char_Array_0[1];
		}
	}
}



void updateVariables(void) {
	BOOL_unsigned_char_Array_0[0] = __VERIFIER_nondet_uchar();
	assume_abort_if_not(BOOL_unsigned_char_Array_0[0] >= 0);
	assume_abort_if_not(BOOL_unsigned_char_Array_0[0] <= 1);
	BOOL_unsigned_char_Array_0[1] = __VERIFIER_nondet_uchar();
	assume_abort_if_not(BOOL_unsigned_char_Array_0[1] >= 0);
	assume_abort_if_not(BOOL_unsigned_char_Array_0[1] <= 1);
	float_Array_0[0] = __VERIFIER_nondet_float();
	assume_abort_if_not((float_Array_0[0] >= -922337.2036854766000e+13F && float_Array_0[0] <= -1.0e-20F) || (float_Array_0[0] <= 9223372.036854766000e+12F && float_Array_0[0] >= 1.0e-20F ));
	float_Array_0[2] = __VERIFIER_nondet_float();
	assume_abort_if_not((float_Array_0[2] >= 4611686.018427388000e+12F && float_Array_0[2] <= -1.0e-20F) || (float_Array_0[2] <= 9223372.036854776000e+12F && float_Array_0[2] >= 1.0e-20F ));
	float_Array_0[3] = __VERIFIER_nondet_float();
	assume_abort_if_not((float_Array_0[3] >= 0.0F && float_Array_0[3] <= -1.0e-20F) || (float_Array_0[3] <= 4611686.018427388000e+12F && float_Array_0[3] >= 1.0e-20F ));
	float_Array_0[4] = __VERIFIER_nondet_float();
	assume_abort_if_not((float_Array_0[4] >= 0.0F && float_Array_0[4] <= -1.0e-20F) || (float_Array_0[4] <= 9223372.036854776000e+12F && float_Array_0[4] >= 1.0e-20F ));
	signed_char_Array_0[1] = __VERIFIER_nondet_char();
	assume_abort_if_not(signed_char_Array_0[1] >= -127);
	assume_abort_if_not(signed_char_Array_0[1] <= 126);
	unsigned_long_int_Array_0[1][0] = __VERIFIER_nondet_ulong();
	assume_abort_if_not(unsigned_long_int_Array_0[1][0] >= 0);
	assume_abort_if_not(unsigned_long_int_Array_0[1][0] <= 4294967294);
	unsigned_long_int_Array_0[0][1] = __VERIFIER_nondet_ulong();
	assume_abort_if_not(unsigned_long_int_Array_0[0][1] >= 0);
	assume_abort_if_not(unsigned_long_int_Array_0[0][1] <= 4294967295);
	unsigned_long_int_Array_0[1][1] = __VERIFIER_nondet_ulong();
	assume_abort_if_not(unsigned_long_int_Array_0[1][1] >= 0);
	assume_abort_if_not(unsigned_long_int_Array_0[1][1] <= 4294967295);
	unsigned_short_int_Array_0[0][0] = __VERIFIER_nondet_ushort();
	assume_abort_if_not(unsigned_short_int_Array_0[0][0] >= 16384);
	assume_abort_if_not(unsigned_short_int_Array_0[0][0] <= 32767);
	unsigned_short_int_Array_0[1][0] = __VERIFIER_nondet_ushort();
	assume_abort_if_not(unsigned_short_int_Array_0[1][0] >= 16383);
	assume_abort_if_not(unsigned_short_int_Array_0[1][0] <= 32768);
	unsigned_short_int_Array_0[0][1] = __VERIFIER_nondet_ushort();
	assume_abort_if_not(unsigned_short_int_Array_0[0][1] >= 0);
	assume_abort_if_not(unsigned_short_int_Array_0[0][1] <= 32767);
	unsigned_short_int_Array_0[1][1] = __VERIFIER_nondet_ushort();
	assume_abort_if_not(unsigned_short_int_Array_0[1][1] >= 0);
	assume_abort_if_not(unsigned_short_int_Array_0[1][1] <= 32767);
	unsigned_short_int_Array_0[0][2] = __VERIFIER_nondet_ushort();
	assume_abort_if_not(unsigned_short_int_Array_0[0][2] >= 0);
	assume_abort_if_not(unsigned_short_int_Array_0[0][2] <= 65534);
}



void updateLastVariables(void) {
}

int property(void) {
	return ((((unsigned_long_int_Array_0[1][1] >= unsigned_long_int_Array_0[0][1]) ? (unsigned_short_int_Array_0[1][2] == ((unsigned short int) (min (128 , unsigned_short_int_Array_0[0][2])))) : (unsigned_short_int_Array_0[1][2] == ((unsigned short int) (min ((unsigned_short_int_Array_0[1][1] + unsigned_short_int_Array_0[0][1]) , unsigned_short_int_Array_0[0][2]))))) && ((unsigned_long_int_Array_0[0][0] >= unsigned_short_int_Array_0[0][1]) ? (float_Array_0[1] == ((float) float_Array_0[0])) : 1)) && ((-64 >= unsigned_long_int_Array_0[0][0]) ? (((-1000 < 256) && ((max (unsigned_long_int_Array_0[0][0] , unsigned_short_int_Array_0[0][1])) > unsigned_short_int_Array_0[0][2])) ? ((unsigned_short_int_Array_0[0][2] < ((unsigned_short_int_Array_0[1][0] + unsigned_short_int_Array_0[0][0]) - unsigned_short_int_Array_0[0][1])) ? (signed_char_Array_0[0] == ((signed char) signed_char_Array_0[1])) : 1) : (signed_char_Array_0[0] == ((signed char) signed_char_Array_0[1]))) : 1)) && ((BOOL_unsigned_char_Array_0[0] && BOOL_unsigned_char_Array_0[1]) ? ((float_Array_0[0] > ((float_Array_0[2] - float_Array_0[3]) - float_Array_0[4])) ? (unsigned_long_int_Array_0[0][0] == ((unsigned long int) unsigned_long_int_Array_0[1][0])) : 1) : (unsigned_long_int_Array_0[0][0] == ((unsigned long int) unsigned_short_int_Array_0[0][1])))
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
