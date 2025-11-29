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
void reach_error(void) { __assert_fail("0", "Req1_Prop1_Batch174Wrapper_P.c", 13, "reach_error"); }
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
unsigned long int var_1_1 = 128;
unsigned long int* var_1_1_Pointer = &(var_1_1);
unsigned long int var_1_2 = 3672536656;
unsigned long int* var_1_2_Pointer = &(var_1_2);
unsigned long int var_1_3 = 2030143942;
unsigned long int* var_1_3_Pointer = &(var_1_3);
unsigned long int var_1_4 = 16;
unsigned long int* var_1_4_Pointer = &(var_1_4);
unsigned long int var_1_5 = 2;
unsigned long int* var_1_5_Pointer = &(var_1_5);
unsigned char var_1_6 = 0;
unsigned char* var_1_6_Pointer = &(var_1_6);
unsigned long int var_1_7 = 16;
unsigned long int* var_1_7_Pointer = &(var_1_7);
signed long int var_1_8 = -10;
signed long int* var_1_8_Pointer = &(var_1_8);
float var_1_9 = 32.1;
float* var_1_9_Pointer = &(var_1_9);
signed long int var_1_10 = 1638083155;
signed long int* var_1_10_Pointer = &(var_1_10);
signed long int var_1_11 = 32;
signed long int* var_1_11_Pointer = &(var_1_11);
signed long int var_1_12 = 25;
signed long int* var_1_12_Pointer = &(var_1_12);
signed short int var_1_13 = -64;
signed short int* var_1_13_Pointer = &(var_1_13);
signed short int var_1_14 = 100;
signed short int* var_1_14_Pointer = &(var_1_14);
signed short int var_1_15 = 32;
signed short int* var_1_15_Pointer = &(var_1_15);
signed short int var_1_16 = 25;
signed short int* var_1_16_Pointer = &(var_1_16);
signed short int var_1_17 = 8;
signed short int* var_1_17_Pointer = &(var_1_17);

// Calibration values

// Last'ed variables

// Additional functions


void initially(void) {
}



void step(void) {
	// From: Req1Batch174Wrapper_P
	(*(var_1_1_Pointer)) = ((*(var_1_2_Pointer)) - ((*(var_1_3_Pointer)) - (*(var_1_4_Pointer))));


	// From: Req2Batch174Wrapper_P
	if (((*(var_1_4_Pointer)) < (*(var_1_2_Pointer))) || (*(var_1_6_Pointer))) {
		(*(var_1_5_Pointer)) = ((max ((abs ((*(var_1_2_Pointer)))) , 3934615513u)) - (*(var_1_4_Pointer)));
	} else {
		(*(var_1_5_Pointer)) = (*(var_1_7_Pointer));
	}


	// From: Req3Batch174Wrapper_P
	unsigned char stepLocal_0 = (*(var_1_5_Pointer)) > 1000000000u;
	if (stepLocal_0 || ((- 4.4f) >= (*(var_1_9_Pointer)))) {
		(*(var_1_8_Pointer)) = ((*(var_1_4_Pointer)) - ((*(var_1_10_Pointer)) - (min ((*(var_1_11_Pointer)) , (*(var_1_12_Pointer))))));
	} else {
		if ((*(var_1_6_Pointer))) {
			(*(var_1_8_Pointer)) = (*(var_1_12_Pointer));
		} else {
			(*(var_1_8_Pointer)) = (*(var_1_11_Pointer));
		}
	}


	// From: Req4Batch174Wrapper_P
	unsigned long int stepLocal_1 = (*(var_1_2_Pointer));
	if ((*(var_1_7_Pointer)) >= stepLocal_1) {
		if ((*(var_1_6_Pointer))) {
			(*(var_1_13_Pointer)) = (min ((*(var_1_14_Pointer)) , (*(var_1_15_Pointer))));
		}
	} else {
		(*(var_1_13_Pointer)) = ((*(var_1_16_Pointer)) + (*(var_1_17_Pointer)));
	}
}



void updateVariables(void) {
	var_1_2 = __VERIFIER_nondet_ulong();
	assume_abort_if_not(var_1_2 >= 2147483647);
	assume_abort_if_not(var_1_2 <= 4294967294);
	var_1_3 = __VERIFIER_nondet_ulong();
	assume_abort_if_not(var_1_3 >= 1073741823);
	assume_abort_if_not(var_1_3 <= 2147483647);
	var_1_4 = __VERIFIER_nondet_ulong();
	assume_abort_if_not(var_1_4 >= 0);
	assume_abort_if_not(var_1_4 <= 1073741823);
	var_1_6 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_6 >= 0);
	assume_abort_if_not(var_1_6 <= 1);
	var_1_7 = __VERIFIER_nondet_ulong();
	assume_abort_if_not(var_1_7 >= 0);
	assume_abort_if_not(var_1_7 <= 4294967294);
	var_1_9 = __VERIFIER_nondet_float();
	assume_abort_if_not((var_1_9 >= -922337.2036854776000e+13F && var_1_9 <= -1.0e-20F) || (var_1_9 <= 9223372.036854776000e+12F && var_1_9 >= 1.0e-20F ));
	var_1_10 = __VERIFIER_nondet_long();
	assume_abort_if_not(var_1_10 >= 1073741823);
	assume_abort_if_not(var_1_10 <= 2147483646);
	var_1_11 = __VERIFIER_nondet_long();
	assume_abort_if_not(var_1_11 >= 0);
	assume_abort_if_not(var_1_11 <= 1073741823);
	var_1_12 = __VERIFIER_nondet_long();
	assume_abort_if_not(var_1_12 >= 0);
	assume_abort_if_not(var_1_12 <= 1073741823);
	var_1_14 = __VERIFIER_nondet_short();
	assume_abort_if_not(var_1_14 >= -32767);
	assume_abort_if_not(var_1_14 <= 32766);
	var_1_15 = __VERIFIER_nondet_short();
	assume_abort_if_not(var_1_15 >= -32767);
	assume_abort_if_not(var_1_15 <= 32766);
	var_1_16 = __VERIFIER_nondet_short();
	assume_abort_if_not(var_1_16 >= -16383);
	assume_abort_if_not(var_1_16 <= 16383);
	var_1_17 = __VERIFIER_nondet_short();
	assume_abort_if_not(var_1_17 >= -16383);
	assume_abort_if_not(var_1_17 <= 16383);
}



void updateLastVariables(void) {
}

int property(void) {
	return ((((*(var_1_1_Pointer)) == ((unsigned long int) ((*(var_1_2_Pointer)) - ((*(var_1_3_Pointer)) - (*(var_1_4_Pointer)))))) && ((((*(var_1_4_Pointer)) < (*(var_1_2_Pointer))) || (*(var_1_6_Pointer))) ? ((*(var_1_5_Pointer)) == ((unsigned long int) ((max ((abs ((*(var_1_2_Pointer)))) , 3934615513u)) - (*(var_1_4_Pointer))))) : ((*(var_1_5_Pointer)) == ((unsigned long int) (*(var_1_7_Pointer)))))) && ((((*(var_1_5_Pointer)) > 1000000000u) || ((- 4.4f) >= (*(var_1_9_Pointer)))) ? ((*(var_1_8_Pointer)) == ((signed long int) ((*(var_1_4_Pointer)) - ((*(var_1_10_Pointer)) - (min ((*(var_1_11_Pointer)) , (*(var_1_12_Pointer)))))))) : ((*(var_1_6_Pointer)) ? ((*(var_1_8_Pointer)) == ((signed long int) (*(var_1_12_Pointer)))) : ((*(var_1_8_Pointer)) == ((signed long int) (*(var_1_11_Pointer))))))) && (((*(var_1_7_Pointer)) >= (*(var_1_2_Pointer))) ? ((*(var_1_6_Pointer)) ? ((*(var_1_13_Pointer)) == ((signed short int) (min ((*(var_1_14_Pointer)) , (*(var_1_15_Pointer)))))) : 1) : ((*(var_1_13_Pointer)) == ((signed short int) ((*(var_1_16_Pointer)) + (*(var_1_17_Pointer))))))
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
