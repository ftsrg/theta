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
void reach_error(void) { __assert_fail("0", "Req1_Prop1_Batch15no_floats.c", 13, "reach_error"); }
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
signed char var_1_1 = -128;
unsigned char var_1_2 = 1;
unsigned char var_1_6 = 1;
signed char var_1_7 = 8;
unsigned long int var_1_8 = 1;
unsigned long int var_1_9 = 1885310857;
signed long int var_1_10 = -10;
signed long int var_1_11 = -5;
signed short int var_1_12 = 128;
signed short int var_1_13 = 10000;
signed long int var_1_14 = 1000;
signed long int var_1_15 = 0;
signed long int var_1_16 = 64;
signed long int var_1_17 = 0;
signed long int var_1_18 = 32;

// Calibration values

// Last'ed variables
signed long int last_1_var_1_10 = -10;

// Additional functions


void initially(void) {
}



void step(void) {
	// From: Req2Batch15no_floats
	if (var_1_2) {
		var_1_8 = ((1514707036u + (abs (var_1_9))) - last_1_var_1_10);
	} else {
		var_1_8 = (max (last_1_var_1_10 , var_1_9));
	}


	// From: Req3Batch15no_floats
	if (var_1_2) {
		var_1_10 = (var_1_8 + (abs (var_1_7)));
	}


	// From: Req1Batch15no_floats
	unsigned char stepLocal_1 = (~ var_1_10) >= var_1_8;
	unsigned long int stepLocal_0 = var_1_8;
	if (var_1_2 || stepLocal_1) {
		if (stepLocal_0 < var_1_10) {
			if (! var_1_6) {
				var_1_1 = var_1_7;
			}
		} else {
			var_1_1 = 2;
		}
	} else {
		var_1_1 = var_1_7;
	}


	// From: Req4Batch15no_floats
	signed long int stepLocal_2 = var_1_12 - var_1_13;
	if (stepLocal_2 > var_1_8) {
		var_1_11 = ((max (var_1_14 , (var_1_15 + var_1_16))) - (var_1_17 + var_1_18));
	} else {
		var_1_11 = var_1_17;
	}
}



void updateVariables(void) {
	var_1_2 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_2 >= 0);
	assume_abort_if_not(var_1_2 <= 1);
	var_1_6 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_6 >= 0);
	assume_abort_if_not(var_1_6 <= 1);
	var_1_7 = __VERIFIER_nondet_char();
	assume_abort_if_not(var_1_7 >= -127);
	assume_abort_if_not(var_1_7 <= 126);
	var_1_9 = __VERIFIER_nondet_ulong();
	assume_abort_if_not(var_1_9 >= 1073741824);
	assume_abort_if_not(var_1_9 <= 2147483647);
	var_1_12 = __VERIFIER_nondet_short();
	assume_abort_if_not(var_1_12 >= -1);
	assume_abort_if_not(var_1_12 <= 32767);
	var_1_13 = __VERIFIER_nondet_short();
	assume_abort_if_not(var_1_13 >= 0);
	assume_abort_if_not(var_1_13 <= 32767);
	var_1_14 = __VERIFIER_nondet_long();
	assume_abort_if_not(var_1_14 >= 0);
	assume_abort_if_not(var_1_14 <= 2147483647);
	var_1_15 = __VERIFIER_nondet_long();
	assume_abort_if_not(var_1_15 >= 0);
	assume_abort_if_not(var_1_15 <= 2147483647);
	var_1_16 = __VERIFIER_nondet_long();
	assume_abort_if_not(var_1_16 >= 0);
	assume_abort_if_not(var_1_16 <= 2147483647);
	var_1_17 = __VERIFIER_nondet_long();
	assume_abort_if_not(var_1_17 >= 0);
	assume_abort_if_not(var_1_17 <= 2147483647);
	var_1_18 = __VERIFIER_nondet_long();
	assume_abort_if_not(var_1_18 >= 0);
	assume_abort_if_not(var_1_18 <= 2147483647);
}



void updateLastVariables(void) {
	last_1_var_1_10 = var_1_10;
}

int property(void) {
	return ((((var_1_2 || ((~ var_1_10) >= var_1_8)) ? ((var_1_8 < var_1_10) ? ((! var_1_6) ? (var_1_1 == ((signed char) var_1_7)) : 1) : (var_1_1 == ((signed char) 2))) : (var_1_1 == ((signed char) var_1_7))) && (var_1_2 ? (var_1_8 == ((unsigned long int) ((1514707036u + (abs (var_1_9))) - last_1_var_1_10))) : (var_1_8 == ((unsigned long int) (max (last_1_var_1_10 , var_1_9)))))) && (var_1_2 ? (var_1_10 == ((signed long int) (var_1_8 + (abs (var_1_7))))) : 1)) && (((var_1_12 - var_1_13) > var_1_8) ? (var_1_11 == ((signed long int) ((max (var_1_14 , (var_1_15 + var_1_16))) - (var_1_17 + var_1_18)))) : (var_1_11 == ((signed long int) var_1_17)))
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
