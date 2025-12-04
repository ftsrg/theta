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
void reach_error(void) { __assert_fail("0", "Req1_Prop1_Batch109100_1loop.c", 13, "reach_error"); }
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
unsigned short int var_1_1 = 10;
double var_1_2 = 99999999.2;
double var_1_3 = 256.5;
unsigned short int var_1_5 = 100;
unsigned char var_1_6 = 0;
signed char var_1_7 = 8;
signed long int var_1_8 = 1;
unsigned char var_1_11 = 0;
unsigned long int var_1_12 = 25;
unsigned long int var_1_13 = 1;
unsigned long int var_1_14 = 1173913989;
unsigned long int var_1_15 = 2364533249;
unsigned long int var_1_16 = 1941942463;
unsigned char var_1_17 = 0;
unsigned short int var_1_18 = 8;
signed short int var_1_19 = 4;
signed long int var_1_20 = -32;
signed long int var_1_21 = 1000000000;
float var_1_22 = 64.8;
float var_1_23 = 31.125;
float var_1_24 = 25.5;
float var_1_25 = 10.5;
float var_1_26 = 7.6;
float var_1_27 = 9.1;
signed short int var_1_28 = -256;
signed short int var_1_29 = 8;
signed char var_1_31 = 1;
signed char var_1_32 = 0;
double var_1_33 = 0.5;
double var_1_34 = 256.5;
signed long int var_1_35 = -2;
unsigned char var_1_36 = 0;

// Calibration values

// Last'ed variables
unsigned char last_1_var_1_6 = 0;
unsigned char last_1_var_1_17 = 0;
signed long int last_1_var_1_35 = -2;

// Additional functions


void initially(void) {
}



void step(void) {
	// From: Req3Batch109100_1loop
	unsigned char stepLocal_2 = last_1_var_1_6;
	unsigned char stepLocal_1 = ! last_1_var_1_6;
	if ((var_1_5 == var_1_7) || stepLocal_2) {
		if (stepLocal_1 || var_1_11) {
			var_1_12 = (var_1_13 + (min ((last_1_var_1_35 + var_1_7) , (var_1_14 - var_1_5))));
		}
	} else {
		var_1_12 = ((max (var_1_15 , (2069588410u + var_1_16))) - (var_1_14 - var_1_5));
	}


	// From: Req2Batch109100_1loop
	signed long int stepLocal_0 = var_1_7 >> var_1_8;
	if (stepLocal_0 >= last_1_var_1_35) {
		var_1_6 = (last_1_var_1_17 && var_1_11);
	}


	// From: Req7Batch109100_1loop
	var_1_22 = (min (var_1_23 , ((min (var_1_24 , var_1_25)) + (min (var_1_26 , var_1_27)))));


	// From: Req8Batch109100_1loop
	if ((var_1_25 * var_1_27) > var_1_23) {
		var_1_28 = ((min (var_1_8 , var_1_7)) - var_1_29);
	} else {
		if ((1u ^ var_1_12) != (var_1_14 << (var_1_31 - var_1_32))) {
			var_1_28 = (abs (var_1_29));
		} else {
			var_1_28 = var_1_31;
		}
	}


	// From: Req9Batch109100_1loop
	var_1_33 = (((min (5.75 , 1.5)) + var_1_34) + var_1_24);


	// From: Req1Batch109100_1loop
	if ((5.45 * var_1_33) == (10.8 + (128.625 / var_1_3))) {
		if (var_1_33 < (var_1_3 * var_1_33)) {
			var_1_1 = 100;
		} else {
			var_1_1 = var_1_5;
		}
	}


	// From: Req5Batch109100_1loop
	unsigned short int stepLocal_3 = var_1_1;
	if ((var_1_7 - (max (var_1_8 , var_1_19))) < stepLocal_3) {
		var_1_18 = ((55943 - var_1_8) - var_1_7);
	} else {
		var_1_18 = var_1_8;
	}


	// From: Req11Batch109100_1loop
	if (var_1_27 < (abs (var_1_33 * var_1_22))) {
		if (var_1_6) {
			if (((var_1_2 + var_1_23) > (var_1_24 * var_1_25)) || ((16 + var_1_14) <= var_1_12)) {
				var_1_36 = var_1_11;
			} else {
				var_1_36 = (! var_1_11);
			}
		} else {
			var_1_36 = var_1_11;
		}
	} else {
		var_1_36 = var_1_11;
	}


	// From: Req4Batch109100_1loop
	if (var_1_36) {
		if (var_1_6 && (var_1_12 <= var_1_18)) {
			var_1_17 = (var_1_6 && var_1_11);
		} else {
			var_1_17 = var_1_11;
		}
	}


	// From: Req6Batch109100_1loop
	if (var_1_17) {
		if (var_1_14 >= (var_1_1 / var_1_16)) {
			var_1_20 = ((var_1_8 - (var_1_21 - var_1_7)) + (var_1_19 - var_1_1));
		}
	}


	// From: Req10Batch109100_1loop
	if (var_1_18 >= var_1_20) {
		if (! var_1_36) {
			var_1_35 = (min (var_1_1 , var_1_32));
		}
	}
}



void updateVariables(void) {
	var_1_2 = __VERIFIER_nondet_double();
	assume_abort_if_not((var_1_2 >= -922337.2036854776000e+13F && var_1_2 <= -1.0e-20F) || (var_1_2 <= 9223372.036854776000e+12F && var_1_2 >= 1.0e-20F ));
	var_1_3 = __VERIFIER_nondet_double();
	assume_abort_if_not((var_1_3 >= -922337.2036854776000e+13F && var_1_3 <= -1.0e-20F) || (var_1_3 <= 9223372.036854776000e+12F && var_1_3 >= 1.0e-20F ));
	assume_abort_if_not(var_1_3 != 0.0F);
	var_1_5 = __VERIFIER_nondet_ushort();
	assume_abort_if_not(var_1_5 >= 0);
	assume_abort_if_not(var_1_5 <= 65534);
	var_1_7 = __VERIFIER_nondet_char();
	assume_abort_if_not(var_1_7 >= 0);
	assume_abort_if_not(var_1_7 <= 127);
	var_1_8 = __VERIFIER_nondet_long();
	assume_abort_if_not(var_1_8 >= 1);
	assume_abort_if_not(var_1_8 <= 6);
	var_1_11 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_11 >= 0);
	assume_abort_if_not(var_1_11 <= 0);
	var_1_13 = __VERIFIER_nondet_ulong();
	assume_abort_if_not(var_1_13 >= 0);
	assume_abort_if_not(var_1_13 <= 2147483647);
	var_1_14 = __VERIFIER_nondet_ulong();
	assume_abort_if_not(var_1_14 >= 1073741823);
	assume_abort_if_not(var_1_14 <= 2147483647);
	var_1_15 = __VERIFIER_nondet_ulong();
	assume_abort_if_not(var_1_15 >= 2147483647);
	assume_abort_if_not(var_1_15 <= 4294967294);
	var_1_16 = __VERIFIER_nondet_ulong();
	assume_abort_if_not(var_1_16 >= 1073741824);
	assume_abort_if_not(var_1_16 <= 2147483647);
	var_1_19 = __VERIFIER_nondet_short();
	assume_abort_if_not(var_1_19 >= 0);
	assume_abort_if_not(var_1_19 <= 32767);
	var_1_21 = __VERIFIER_nondet_long();
	assume_abort_if_not(var_1_21 >= 536870911);
	assume_abort_if_not(var_1_21 <= 1073741823);
	var_1_23 = __VERIFIER_nondet_float();
	assume_abort_if_not((var_1_23 >= -922337.2036854766000e+13F && var_1_23 <= -1.0e-20F) || (var_1_23 <= 9223372.036854766000e+12F && var_1_23 >= 1.0e-20F ));
	var_1_24 = __VERIFIER_nondet_float();
	assume_abort_if_not((var_1_24 >= -461168.6018427383000e+13F && var_1_24 <= -1.0e-20F) || (var_1_24 <= 4611686.018427383000e+12F && var_1_24 >= 1.0e-20F ));
	var_1_25 = __VERIFIER_nondet_float();
	assume_abort_if_not((var_1_25 >= -461168.6018427383000e+13F && var_1_25 <= -1.0e-20F) || (var_1_25 <= 4611686.018427383000e+12F && var_1_25 >= 1.0e-20F ));
	var_1_26 = __VERIFIER_nondet_float();
	assume_abort_if_not((var_1_26 >= -461168.6018427383000e+13F && var_1_26 <= -1.0e-20F) || (var_1_26 <= 4611686.018427383000e+12F && var_1_26 >= 1.0e-20F ));
	var_1_27 = __VERIFIER_nondet_float();
	assume_abort_if_not((var_1_27 >= -461168.6018427383000e+13F && var_1_27 <= -1.0e-20F) || (var_1_27 <= 4611686.018427383000e+12F && var_1_27 >= 1.0e-20F ));
	var_1_29 = __VERIFIER_nondet_short();
	assume_abort_if_not(var_1_29 >= 0);
	assume_abort_if_not(var_1_29 <= 32766);
	var_1_31 = __VERIFIER_nondet_char();
	assume_abort_if_not(var_1_31 >= 0);
	assume_abort_if_not(var_1_31 <= 1);
	var_1_32 = __VERIFIER_nondet_char();
	assume_abort_if_not(var_1_32 >= 0);
	assume_abort_if_not(var_1_32 <= 0);
	var_1_34 = __VERIFIER_nondet_double();
	assume_abort_if_not((var_1_34 >= -230584.3009213691400e+13F && var_1_34 <= -1.0e-20F) || (var_1_34 <= 2305843.009213691400e+12F && var_1_34 >= 1.0e-20F ));
}



void updateLastVariables(void) {
	last_1_var_1_6 = var_1_6;
	last_1_var_1_17 = var_1_17;
	last_1_var_1_35 = var_1_35;
}

int property(void) {
	return ((((((((((((5.45 * var_1_33) == (10.8 + (128.625 / var_1_3))) ? ((var_1_33 < (var_1_3 * var_1_33)) ? (var_1_1 == ((unsigned short int) 100)) : (var_1_1 == ((unsigned short int) var_1_5))) : 1) && (((var_1_7 >> var_1_8) >= last_1_var_1_35) ? (var_1_6 == ((unsigned char) (last_1_var_1_17 && var_1_11))) : 1)) && (((var_1_5 == var_1_7) || last_1_var_1_6) ? (((! last_1_var_1_6) || var_1_11) ? (var_1_12 == ((unsigned long int) (var_1_13 + (min ((last_1_var_1_35 + var_1_7) , (var_1_14 - var_1_5)))))) : 1) : (var_1_12 == ((unsigned long int) ((max (var_1_15 , (2069588410u + var_1_16))) - (var_1_14 - var_1_5)))))) && (var_1_36 ? ((var_1_6 && (var_1_12 <= var_1_18)) ? (var_1_17 == ((unsigned char) (var_1_6 && var_1_11))) : (var_1_17 == ((unsigned char) var_1_11))) : 1)) && (((var_1_7 - (max (var_1_8 , var_1_19))) < var_1_1) ? (var_1_18 == ((unsigned short int) ((55943 - var_1_8) - var_1_7))) : (var_1_18 == ((unsigned short int) var_1_8)))) && (var_1_17 ? ((var_1_14 >= (var_1_1 / var_1_16)) ? (var_1_20 == ((signed long int) ((var_1_8 - (var_1_21 - var_1_7)) + (var_1_19 - var_1_1)))) : 1) : 1)) && (var_1_22 == ((float) (min (var_1_23 , ((min (var_1_24 , var_1_25)) + (min (var_1_26 , var_1_27)))))))) && (((var_1_25 * var_1_27) > var_1_23) ? (var_1_28 == ((signed short int) ((min (var_1_8 , var_1_7)) - var_1_29))) : (((1u ^ var_1_12) != (var_1_14 << (var_1_31 - var_1_32))) ? (var_1_28 == ((signed short int) (abs (var_1_29)))) : (var_1_28 == ((signed short int) var_1_31))))) && (var_1_33 == ((double) (((min (5.75 , 1.5)) + var_1_34) + var_1_24)))) && ((var_1_18 >= var_1_20) ? ((! var_1_36) ? (var_1_35 == ((signed long int) (min (var_1_1 , var_1_32)))) : 1) : 1)) && ((var_1_27 < (abs (var_1_33 * var_1_22))) ? (var_1_6 ? ((((var_1_2 + var_1_23) > (var_1_24 * var_1_25)) || ((16 + var_1_14) <= var_1_12)) ? (var_1_36 == ((unsigned char) var_1_11)) : (var_1_36 == ((unsigned char) (! var_1_11)))) : (var_1_36 == ((unsigned char) var_1_11))) : (var_1_36 == ((unsigned char) var_1_11)))
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
