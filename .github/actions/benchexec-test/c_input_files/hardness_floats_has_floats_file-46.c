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
void reach_error(void) { __assert_fail("0", "Req1_Prop1_Batch46has_floats.c", 13, "reach_error"); }
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
unsigned char var_1_1 = 1;
unsigned char var_1_4 = 0;
unsigned char var_1_5 = 0;
unsigned char var_1_6 = 1;
unsigned char var_1_7 = 0;
signed short int var_1_8 = 32;
signed long int var_1_10 = -25;
signed short int var_1_12 = 0;
signed short int var_1_13 = -5;
signed short int var_1_14 = 128;
double var_1_15 = -10.0;
double var_1_16 = 8.0;
double var_1_17 = 0.0;
unsigned char var_1_18 = 50;
unsigned char var_1_19 = 10;
unsigned char var_1_20 = 1;
double var_1_21 = -1.0;
signed long int var_1_22 = -10;

// Calibration values

// Last'ed variables
double last_1_var_1_15 = -10.0;

// Additional functions


void initially(void) {
}



void step(void) {
	// From: Req1Batch46has_floats
	if ((- last_1_var_1_15) >= last_1_var_1_15) {
		var_1_1 = (var_1_4 || var_1_5);
	} else {
		var_1_1 = (var_1_6 && (var_1_4 || (var_1_5 || var_1_7)));
	}


	// From: Req3Batch46has_floats
	if (var_1_1) {
		var_1_15 = (var_1_16 - var_1_17);
	}


	// From: Req4Batch46has_floats
	if (var_1_5) {
		if (var_1_6) {
			var_1_18 = (50 + var_1_19);
		} else {
			var_1_18 = (min (var_1_19 , var_1_20));
		}
	} else {
		var_1_18 = (abs (var_1_20));
	}


	// From: Req5Batch46has_floats
	var_1_21 = var_1_16;


	// From: Req6Batch46has_floats
	var_1_22 = var_1_12;


	// From: Req2Batch46has_floats
	if ((var_1_22 / var_1_10) != var_1_22) {
		var_1_8 = (min (((abs (var_1_12)) + var_1_13) , var_1_14));
	} else {
		var_1_8 = var_1_13;
	}
}



void updateVariables(void) {
	var_1_4 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_4 >= 0);
	assume_abort_if_not(var_1_4 <= 0);
	var_1_5 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_5 >= 0);
	assume_abort_if_not(var_1_5 <= 0);
	var_1_6 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_6 >= 1);
	assume_abort_if_not(var_1_6 <= 1);
	var_1_7 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_7 >= 1);
	assume_abort_if_not(var_1_7 <= 1);
	var_1_10 = __VERIFIER_nondet_long();
	assume_abort_if_not(var_1_10 >= -2147483648);
	assume_abort_if_not(var_1_10 <= 2147483647);
	assume_abort_if_not(var_1_10 != 0);
	var_1_12 = __VERIFIER_nondet_short();
	assume_abort_if_not(var_1_12 >= -16383);
	assume_abort_if_not(var_1_12 <= 16383);
	var_1_13 = __VERIFIER_nondet_short();
	assume_abort_if_not(var_1_13 >= -16383);
	assume_abort_if_not(var_1_13 <= 16383);
	var_1_14 = __VERIFIER_nondet_short();
	assume_abort_if_not(var_1_14 >= -32767);
	assume_abort_if_not(var_1_14 <= 32766);
	var_1_16 = __VERIFIER_nondet_double();
	assume_abort_if_not((var_1_16 >= 0.0F && var_1_16 <= -1.0e-20F) || (var_1_16 <= 9223372.036854766000e+12F && var_1_16 >= 1.0e-20F ));
	var_1_17 = __VERIFIER_nondet_double();
	assume_abort_if_not((var_1_17 >= 0.0F && var_1_17 <= -1.0e-20F) || (var_1_17 <= 9223372.036854766000e+12F && var_1_17 >= 1.0e-20F ));
	var_1_19 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_19 >= 0);
	assume_abort_if_not(var_1_19 <= 127);
	var_1_20 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_20 >= 0);
	assume_abort_if_not(var_1_20 <= 254);
}



void updateLastVariables(void) {
	last_1_var_1_15 = var_1_15;
}

int property(void) {
	return (((((((- last_1_var_1_15) >= last_1_var_1_15) ? (var_1_1 == ((unsigned char) (var_1_4 || var_1_5))) : (var_1_1 == ((unsigned char) (var_1_6 && (var_1_4 || (var_1_5 || var_1_7)))))) && (((var_1_22 / var_1_10) != var_1_22) ? (var_1_8 == ((signed short int) (min (((abs (var_1_12)) + var_1_13) , var_1_14)))) : (var_1_8 == ((signed short int) var_1_13)))) && (var_1_1 ? (var_1_15 == ((double) (var_1_16 - var_1_17))) : 1)) && (var_1_5 ? (var_1_6 ? (var_1_18 == ((unsigned char) (50 + var_1_19))) : (var_1_18 == ((unsigned char) (min (var_1_19 , var_1_20))))) : (var_1_18 == ((unsigned char) (abs (var_1_20)))))) && (var_1_21 == ((double) var_1_16))) && (var_1_22 == ((signed long int) var_1_12))
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
