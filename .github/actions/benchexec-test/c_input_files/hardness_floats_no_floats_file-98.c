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
void reach_error(void) { __assert_fail("0", "Req1_Prop1_Batch98no_floats.c", 13, "reach_error"); }
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
signed long int var_1_1 = -10;
signed long int var_1_4 = 500;
signed short int var_1_5 = 16;
signed short int var_1_6 = 10;
signed short int var_1_7 = 5;
unsigned char var_1_8 = 0;
unsigned char var_1_9 = 128;
unsigned char var_1_10 = 16;
unsigned char var_1_11 = 0;
unsigned char var_1_12 = 0;
signed short int var_1_13 = 5;
signed short int var_1_14 = 1;
signed short int var_1_15 = 64;
unsigned short int var_1_16 = 128;
unsigned long int var_1_17 = 10000;
unsigned char var_1_18 = 16;

// Calibration values

// Last'ed variables

// Additional functions


void initially(void) {
}



void step(void) {
	// From: Req5Batch98no_floats
	var_1_16 = var_1_6;


	// From: Req7Batch98no_floats
	var_1_18 = 16;


	// From: Req4Batch98no_floats
	var_1_13 = (var_1_6 + ((max (var_1_14 , var_1_15)) - var_1_18));


	// From: Req6Batch98no_floats
	var_1_17 = var_1_18;


	// From: Req1Batch98no_floats
	if (var_1_13 != (abs (var_1_16))) {
		if ((min (16u , var_1_13)) >= var_1_16) {
			var_1_1 = var_1_4;
		}
	} else {
		var_1_1 = var_1_4;
	}


	// From: Req2Batch98no_floats
	if (var_1_1 < (- (- var_1_4))) {
		var_1_5 = (var_1_18 + var_1_17);
	} else {
		var_1_5 = ((var_1_17 + (max (var_1_18 , var_1_6))) - var_1_7);
	}


	// From: Req3Batch98no_floats
	signed long int stepLocal_0 = var_1_9 - var_1_10;
	if (var_1_13 != stepLocal_0) {
		var_1_8 = (var_1_11 || var_1_12);
	}
}



void updateVariables(void) {
	var_1_4 = __VERIFIER_nondet_long();
	assume_abort_if_not(var_1_4 >= -2147483648);
	assume_abort_if_not(var_1_4 <= 2147483647);
	var_1_6 = __VERIFIER_nondet_short();
	assume_abort_if_not(var_1_6 >= 0);
	assume_abort_if_not(var_1_6 <= 16383);
	var_1_7 = __VERIFIER_nondet_short();
	assume_abort_if_not(var_1_7 >= 0);
	assume_abort_if_not(var_1_7 <= 32766);
	var_1_9 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_9 >= 127);
	assume_abort_if_not(var_1_9 <= 255);
	var_1_10 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_10 >= 0);
	assume_abort_if_not(var_1_10 <= 127);
	var_1_11 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_11 >= 0);
	assume_abort_if_not(var_1_11 <= 0);
	var_1_12 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_12 >= 0);
	assume_abort_if_not(var_1_12 <= 0);
	var_1_14 = __VERIFIER_nondet_short();
	assume_abort_if_not(var_1_14 >= 0);
	assume_abort_if_not(var_1_14 <= 16383);
	var_1_15 = __VERIFIER_nondet_short();
	assume_abort_if_not(var_1_15 >= 0);
	assume_abort_if_not(var_1_15 <= 16383);
}



void updateLastVariables(void) {
}

int property(void) {
	return (((((((var_1_13 != (abs (var_1_16))) ? (((min (16u , var_1_13)) >= var_1_16) ? (var_1_1 == ((signed long int) var_1_4)) : 1) : (var_1_1 == ((signed long int) var_1_4))) && ((var_1_1 < (- (- var_1_4))) ? (var_1_5 == ((signed short int) (var_1_18 + var_1_17))) : (var_1_5 == ((signed short int) ((var_1_17 + (max (var_1_18 , var_1_6))) - var_1_7))))) && ((var_1_13 != (var_1_9 - var_1_10)) ? (var_1_8 == ((unsigned char) (var_1_11 || var_1_12))) : 1)) && (var_1_13 == ((signed short int) (var_1_6 + ((max (var_1_14 , var_1_15)) - var_1_18))))) && (var_1_16 == ((unsigned short int) var_1_6))) && (var_1_17 == ((unsigned long int) var_1_18))) && (var_1_18 == ((unsigned char) 16))
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
