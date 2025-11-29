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
void reach_error(void) { __assert_fail("0", "Req1_Prop1_Batch105Amount250.c", 13, "reach_error"); }
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
unsigned short int var_1_1 = 4;
unsigned short int var_1_3 = 4;
unsigned short int var_1_4 = 16;
unsigned short int var_1_5 = 8;
float var_1_6 = 5.6;
float var_1_7 = 8.15;
float var_1_8 = -0.6;
unsigned short int var_1_9 = 45213;
signed char var_1_10 = 32;
signed char var_1_11 = 1;
signed char var_1_12 = 1;
signed char var_1_13 = 8;
signed char var_1_14 = 0;
unsigned char var_1_16 = 32;
unsigned char var_1_18 = 200;
unsigned char var_1_19 = 10;
float var_1_20 = 500.6;
float var_1_21 = 4.4;
signed short int var_1_22 = -4;
unsigned char var_1_23 = 4;
float var_1_24 = 15.125;
float var_1_25 = 255.594;
unsigned char var_1_26 = 100;
unsigned char var_1_27 = 64;
signed long int var_1_28 = -8;
signed long int var_1_29 = 128;
signed long int var_1_30 = 10000;
unsigned char var_1_31 = 0;
unsigned char var_1_32 = 1;
unsigned char var_1_33 = 0;
unsigned char var_1_34 = 5;
unsigned char var_1_35 = 5;
unsigned char var_1_36 = 64;
unsigned char var_1_37 = 64;
signed long int var_1_38 = 64;
signed short int var_1_39 = -1;
signed short int var_1_40 = 21790;
signed long int var_1_41 = 64;
signed char var_1_42 = -50;
signed long int var_1_43 = 1631277124;
signed char var_1_44 = 2;
float var_1_45 = 9.5;
float var_1_46 = 24.6;
float var_1_47 = 2.8;
signed char var_1_48 = 64;
signed char var_1_49 = 8;
double var_1_50 = 1.125;
double var_1_51 = 4.15;
double var_1_52 = 0.75;
float var_1_53 = 7.6;
double var_1_54 = 63.5;
double var_1_55 = 99.75;
double var_1_56 = 256.9;
unsigned short int var_1_57 = 64;
unsigned short int var_1_58 = 5;
unsigned short int var_1_59 = 8;
unsigned char var_1_60 = 0;
unsigned char var_1_61 = 0;
unsigned long int var_1_62 = 16;
unsigned char var_1_63 = 0;

// Calibration values

// Last'ed variables
unsigned char last_1_var_1_16 = 32;
signed long int last_1_var_1_28 = -8;
unsigned char last_1_var_1_35 = 5;
signed long int last_1_var_1_41 = 64;
unsigned short int last_1_var_1_58 = 5;
unsigned long int last_1_var_1_62 = 16;

// Additional functions


void initially(void) {
}



void step(void) {
	// From: Req13Batch105Amount250
	signed long int stepLocal_6 = 32 * last_1_var_1_16;
	if (last_1_var_1_62 <= stepLocal_6) {
		var_1_39 = (var_1_18 - (var_1_40 - var_1_13));
	}


	// From: Req22Batch105Amount250
	var_1_60 = ((256 > var_1_39) && var_1_61);


	// From: Req5Batch105Amount250
	if (var_1_20 < ((var_1_24 - var_1_25) / var_1_21)) {
		if (((16.5f - var_1_24) * var_1_25) >= (- (var_1_20 / 63.25f))) {
			var_1_23 = ((min (var_1_13 , (var_1_26 - var_1_19))) + var_1_27);
		}
	} else {
		var_1_23 = var_1_26;
	}


	// From: Req10Batch105Amount250
	if (var_1_20 >= (var_1_24 - var_1_25)) {
		var_1_34 = (var_1_13 + (min ((min (var_1_27 , 64)) , (abs (10)))));
	} else {
		var_1_34 = (var_1_18 - var_1_13);
	}


	// From: Req16Batch105Amount250
	if (var_1_33) {
		var_1_50 = (var_1_51 + var_1_52);
	}


	// From: Req21Batch105Amount250
	var_1_59 = (min (var_1_18 , var_1_4));


	// From: Req23Batch105Amount250
	var_1_62 = var_1_36;


	// From: Req24Batch105Amount250
	var_1_63 = var_1_33;


	// From: Req20Batch105Amount250
	signed long int stepLocal_11 = (max (var_1_59 , var_1_11)) * var_1_18;
	signed long int stepLocal_10 = min (var_1_18 , -5);
	if (stepLocal_11 == var_1_62) {
		if (stepLocal_10 >= ((last_1_var_1_58 | var_1_5) | var_1_59)) {
			var_1_58 = var_1_18;
		} else {
			var_1_58 = var_1_39;
		}
	}


	// From: Req6Batch105Amount250
	signed long int stepLocal_1 = var_1_3 + var_1_34;
	if ((var_1_18 & last_1_var_1_28) != stepLocal_1) {
		var_1_28 = (abs (var_1_26));
	}


	// From: Req17Batch105Amount250
	unsigned char stepLocal_8 = var_1_63 || var_1_32;
	if (stepLocal_8 && var_1_63) {
		var_1_53 = (var_1_52 + 1000.2f);
	}


	// From: Req18Batch105Amount250
	signed long int stepLocal_9 = -1000000;
	if (((var_1_28 + var_1_44) % var_1_43) == stepLocal_9) {
		var_1_54 = (max (var_1_51 , (var_1_55 - var_1_56)));
	} else {
		var_1_54 = (var_1_55 - var_1_56);
	}


	// From: Req12Batch105Amount250
	if (var_1_21 >= var_1_24) {
		var_1_38 = ((min ((var_1_13 - var_1_58) , var_1_26)) + var_1_59);
	} else {
		var_1_38 = (var_1_59 - var_1_18);
	}


	// From: Req15Batch105Amount250
	if ((var_1_21 * var_1_54) < 63.75f) {
		if ((var_1_18 - (abs (var_1_27))) > (var_1_36 - (var_1_43 - var_1_58))) {
			var_1_42 = (min ((var_1_14 + var_1_19) , (var_1_13 - var_1_44)));
		}
	} else {
		if (((var_1_25 - var_1_24) / (min (var_1_21 , var_1_20))) != (var_1_45 - (max (var_1_46 , var_1_47)))) {
			if (var_1_28 < var_1_11) {
				var_1_42 = (max ((min ((min (var_1_11 , var_1_14)) , var_1_12)) , (var_1_19 - (var_1_48 - var_1_49))));
			} else {
				var_1_42 = (var_1_19 + (var_1_49 - (abs (var_1_14))));
			}
		} else {
			var_1_42 = (var_1_19 + (min ((-16 + 5) , 2)));
		}
	}


	// From: Req8Batch105Amount250
	signed long int stepLocal_3 = var_1_38;
	if ((var_1_54 + 0.75) <= var_1_24) {
		var_1_30 = var_1_13;
	} else {
		if (stepLocal_3 <= (var_1_34 / var_1_18)) {
			if (var_1_60) {
				var_1_30 = (abs (var_1_38));
			} else {
				var_1_30 = (min (var_1_19 , (var_1_5 - var_1_18)));
			}
		} else {
			var_1_30 = (var_1_13 + var_1_19);
		}
	}


	// From: Req9Batch105Amount250
	signed long int stepLocal_4 = (var_1_39 + var_1_30) - var_1_18;
	if (stepLocal_4 >= (var_1_5 << var_1_14)) {
		var_1_31 = ((var_1_53 < 31.75f) || var_1_32);
	} else {
		var_1_31 = ((! 1) || var_1_33);
	}


	// From: Req1Batch105Amount250
	if (! var_1_31) {
		var_1_1 = ((min (var_1_3 , var_1_4)) + (max (10 , var_1_5)));
	} else {
		if (((max (31.25f , 64.6f)) * var_1_6) > var_1_7) {
			if (var_1_6 > var_1_8) {
				var_1_1 = (max (8 , 16));
			}
		} else {
			if (var_1_6 >= (var_1_7 * var_1_8)) {
				var_1_1 = (var_1_9 - (max (var_1_3 , var_1_4)));
			}
		}
	}


	// From: Req2Batch105Amount250
	if (var_1_4 <= var_1_3) {
		if (1 > (max ((min (var_1_9 , -256)) , var_1_4))) {
			var_1_10 = ((min (var_1_11 , var_1_12)) - var_1_13);
		} else {
			var_1_10 = (min ((var_1_14 + -16) , var_1_12));
		}
	} else {
		if (var_1_63 && var_1_31) {
			var_1_10 = var_1_14;
		} else {
			var_1_10 = var_1_12;
		}
	}


	// From: Req4Batch105Amount250
	if (var_1_31) {
		var_1_22 = (min (var_1_14 , (var_1_18 + (1000 - var_1_39))));
	}


	// From: Req7Batch105Amount250
	unsigned char stepLocal_2 = var_1_63;
	if (stepLocal_2 && var_1_60) {
		var_1_29 = var_1_30;
	} else {
		var_1_29 = (128 + var_1_4);
	}


	// From: Req11Batch105Amount250
	signed long int stepLocal_5 = var_1_11 / 5;
	if (stepLocal_5 < (max ((last_1_var_1_35 + var_1_29) , var_1_28))) {
		var_1_35 = ((max (128 , (var_1_26 + var_1_36))) - (abs (var_1_37 - var_1_19)));
	} else {
		var_1_35 = ((abs (var_1_18)) - 2);
	}


	// From: Req14Batch105Amount250
	unsigned char stepLocal_7 = (var_1_24 / var_1_20) >= var_1_25;
	if (var_1_60) {
		var_1_41 = (last_1_var_1_41 - (var_1_9 + var_1_37));
	} else {
		if ((0u >= 16u) || stepLocal_7) {
			var_1_41 = var_1_22;
		}
	}


	// From: Req3Batch105Amount250
	unsigned char stepLocal_0 = var_1_31 || (4 <= var_1_12);
	if (var_1_31) {
		var_1_16 = (abs (var_1_13));
	} else {
		if (stepLocal_0 || var_1_31) {
			var_1_16 = ((var_1_18 - (50 - var_1_19)) - var_1_13);
		} else {
			if (var_1_50 != (var_1_50 / (min (var_1_20 , var_1_21)))) {
				var_1_16 = (max (var_1_19 , var_1_18));
			} else {
				var_1_16 = (var_1_18 - (max (var_1_13 , var_1_19)));
			}
		}
	}


	// From: Req19Batch105Amount250
	if ((32 % var_1_18) >= (var_1_37 * (var_1_48 + 8))) {
		var_1_57 = (max ((max (var_1_26 , var_1_30)) , ((var_1_44 + var_1_18) + (max (var_1_16 , var_1_4)))));
	} else {
		if (var_1_62 < var_1_48) {
			var_1_57 = var_1_62;
		} else {
			var_1_57 = (abs (1 + (var_1_40 - var_1_19)));
		}
	}
}



void updateVariables(void) {
	var_1_3 = __VERIFIER_nondet_ushort();
	assume_abort_if_not(var_1_3 >= 0);
	assume_abort_if_not(var_1_3 <= 32767);
	var_1_4 = __VERIFIER_nondet_ushort();
	assume_abort_if_not(var_1_4 >= 0);
	assume_abort_if_not(var_1_4 <= 32767);
	var_1_5 = __VERIFIER_nondet_ushort();
	assume_abort_if_not(var_1_5 >= 0);
	assume_abort_if_not(var_1_5 <= 32767);
	var_1_6 = __VERIFIER_nondet_float();
	assume_abort_if_not((var_1_6 >= -922337.2036854776000e+13F && var_1_6 <= -1.0e-20F) || (var_1_6 <= 9223372.036854776000e+12F && var_1_6 >= 1.0e-20F ));
	var_1_7 = __VERIFIER_nondet_float();
	assume_abort_if_not((var_1_7 >= -922337.2036854776000e+13F && var_1_7 <= -1.0e-20F) || (var_1_7 <= 9223372.036854776000e+12F && var_1_7 >= 1.0e-20F ));
	var_1_8 = __VERIFIER_nondet_float();
	assume_abort_if_not((var_1_8 >= -922337.2036854776000e+13F && var_1_8 <= -1.0e-20F) || (var_1_8 <= 9223372.036854776000e+12F && var_1_8 >= 1.0e-20F ));
	var_1_9 = __VERIFIER_nondet_ushort();
	assume_abort_if_not(var_1_9 >= 32767);
	assume_abort_if_not(var_1_9 <= 65534);
	var_1_11 = __VERIFIER_nondet_char();
	assume_abort_if_not(var_1_11 >= -1);
	assume_abort_if_not(var_1_11 <= 126);
	var_1_12 = __VERIFIER_nondet_char();
	assume_abort_if_not(var_1_12 >= -1);
	assume_abort_if_not(var_1_12 <= 126);
	var_1_13 = __VERIFIER_nondet_char();
	assume_abort_if_not(var_1_13 >= 0);
	assume_abort_if_not(var_1_13 <= 126);
	var_1_14 = __VERIFIER_nondet_char();
	assume_abort_if_not(var_1_14 >= -63);
	assume_abort_if_not(var_1_14 <= 63);
	var_1_18 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_18 >= 190);
	assume_abort_if_not(var_1_18 <= 254);
	var_1_19 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_19 >= 0);
	assume_abort_if_not(var_1_19 <= 31);
	var_1_20 = __VERIFIER_nondet_float();
	assume_abort_if_not((var_1_20 >= -922337.2036854776000e+13F && var_1_20 <= -1.0e-20F) || (var_1_20 <= 9223372.036854776000e+12F && var_1_20 >= 1.0e-20F ));
	assume_abort_if_not(var_1_20 != 0.0F);
	var_1_21 = __VERIFIER_nondet_float();
	assume_abort_if_not((var_1_21 >= -922337.2036854776000e+13F && var_1_21 <= -1.0e-20F) || (var_1_21 <= 9223372.036854776000e+12F && var_1_21 >= 1.0e-20F ));
	assume_abort_if_not(var_1_21 != 0.0F);
	var_1_24 = __VERIFIER_nondet_float();
	assume_abort_if_not((var_1_24 >= 0.0F && var_1_24 <= -1.0e-20F) || (var_1_24 <= 9223372.036854776000e+12F && var_1_24 >= 1.0e-20F ));
	var_1_25 = __VERIFIER_nondet_float();
	assume_abort_if_not((var_1_25 >= 0.0F && var_1_25 <= -1.0e-20F) || (var_1_25 <= 9223372.036854776000e+12F && var_1_25 >= 1.0e-20F ));
	var_1_26 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_26 >= 63);
	assume_abort_if_not(var_1_26 <= 127);
	var_1_27 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_27 >= 0);
	assume_abort_if_not(var_1_27 <= 127);
	var_1_32 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_32 >= 1);
	assume_abort_if_not(var_1_32 <= 1);
	var_1_33 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_33 >= 1);
	assume_abort_if_not(var_1_33 <= 1);
	var_1_36 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_36 >= 64);
	assume_abort_if_not(var_1_36 <= 127);
	var_1_37 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_37 >= 63);
	assume_abort_if_not(var_1_37 <= 127);
	var_1_40 = __VERIFIER_nondet_short();
	assume_abort_if_not(var_1_40 >= 16383);
	assume_abort_if_not(var_1_40 <= 32766);
	var_1_43 = __VERIFIER_nondet_long();
	assume_abort_if_not(var_1_43 >= 1073741823);
	assume_abort_if_not(var_1_43 <= 2147483647);
	var_1_44 = __VERIFIER_nondet_char();
	assume_abort_if_not(var_1_44 >= 0);
	assume_abort_if_not(var_1_44 <= 126);
	var_1_45 = __VERIFIER_nondet_float();
	assume_abort_if_not((var_1_45 >= 0.0F && var_1_45 <= -1.0e-20F) || (var_1_45 <= 9223372.036854776000e+12F && var_1_45 >= 1.0e-20F ));
	var_1_46 = __VERIFIER_nondet_float();
	assume_abort_if_not((var_1_46 >= 0.0F && var_1_46 <= -1.0e-20F) || (var_1_46 <= 9223372.036854776000e+12F && var_1_46 >= 1.0e-20F ));
	var_1_47 = __VERIFIER_nondet_float();
	assume_abort_if_not((var_1_47 >= 0.0F && var_1_47 <= -1.0e-20F) || (var_1_47 <= 9223372.036854776000e+12F && var_1_47 >= 1.0e-20F ));
	var_1_48 = __VERIFIER_nondet_char();
	assume_abort_if_not(var_1_48 >= 63);
	assume_abort_if_not(var_1_48 <= 126);
	var_1_49 = __VERIFIER_nondet_char();
	assume_abort_if_not(var_1_49 >= 0);
	assume_abort_if_not(var_1_49 <= 63);
	var_1_51 = __VERIFIER_nondet_double();
	assume_abort_if_not((var_1_51 >= -461168.6018427383000e+13F && var_1_51 <= -1.0e-20F) || (var_1_51 <= 4611686.018427383000e+12F && var_1_51 >= 1.0e-20F ));
	var_1_52 = __VERIFIER_nondet_double();
	assume_abort_if_not((var_1_52 >= -461168.6018427383000e+13F && var_1_52 <= -1.0e-20F) || (var_1_52 <= 4611686.018427383000e+12F && var_1_52 >= 1.0e-20F ));
	var_1_55 = __VERIFIER_nondet_double();
	assume_abort_if_not((var_1_55 >= 0.0F && var_1_55 <= -1.0e-20F) || (var_1_55 <= 9223372.036854766000e+12F && var_1_55 >= 1.0e-20F ));
	var_1_56 = __VERIFIER_nondet_double();
	assume_abort_if_not((var_1_56 >= 0.0F && var_1_56 <= -1.0e-20F) || (var_1_56 <= 9223372.036854766000e+12F && var_1_56 >= 1.0e-20F ));
	var_1_61 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_61 >= 0);
	assume_abort_if_not(var_1_61 <= 0);
}



void updateLastVariables(void) {
	last_1_var_1_16 = var_1_16;
	last_1_var_1_28 = var_1_28;
	last_1_var_1_35 = var_1_35;
	last_1_var_1_41 = var_1_41;
	last_1_var_1_58 = var_1_58;
	last_1_var_1_62 = var_1_62;
}

int property(void) {
	return ((((((((((((((((((((((((! var_1_31) ? (var_1_1 == ((unsigned short int) ((min (var_1_3 , var_1_4)) + (max (10 , var_1_5))))) : ((((max (31.25f , 64.6f)) * var_1_6) > var_1_7) ? ((var_1_6 > var_1_8) ? (var_1_1 == ((unsigned short int) (max (8 , 16)))) : 1) : ((var_1_6 >= (var_1_7 * var_1_8)) ? (var_1_1 == ((unsigned short int) (var_1_9 - (max (var_1_3 , var_1_4))))) : 1))) && ((var_1_4 <= var_1_3) ? ((1 > (max ((min (var_1_9 , -256)) , var_1_4))) ? (var_1_10 == ((signed char) ((min (var_1_11 , var_1_12)) - var_1_13))) : (var_1_10 == ((signed char) (min ((var_1_14 + -16) , var_1_12))))) : ((var_1_63 && var_1_31) ? (var_1_10 == ((signed char) var_1_14)) : (var_1_10 == ((signed char) var_1_12))))) && (var_1_31 ? (var_1_16 == ((unsigned char) (abs (var_1_13)))) : (((var_1_31 || (4 <= var_1_12)) || var_1_31) ? (var_1_16 == ((unsigned char) ((var_1_18 - (50 - var_1_19)) - var_1_13))) : ((var_1_50 != (var_1_50 / (min (var_1_20 , var_1_21)))) ? (var_1_16 == ((unsigned char) (max (var_1_19 , var_1_18)))) : (var_1_16 == ((unsigned char) (var_1_18 - (max (var_1_13 , var_1_19))))))))) && (var_1_31 ? (var_1_22 == ((signed short int) (min (var_1_14 , (var_1_18 + (1000 - var_1_39)))))) : 1)) && ((var_1_20 < ((var_1_24 - var_1_25) / var_1_21)) ? ((((16.5f - var_1_24) * var_1_25) >= (- (var_1_20 / 63.25f))) ? (var_1_23 == ((unsigned char) ((min (var_1_13 , (var_1_26 - var_1_19))) + var_1_27))) : 1) : (var_1_23 == ((unsigned char) var_1_26)))) && (((var_1_18 & last_1_var_1_28) != (var_1_3 + var_1_34)) ? (var_1_28 == ((signed long int) (abs (var_1_26)))) : 1)) && ((var_1_63 && var_1_60) ? (var_1_29 == ((signed long int) var_1_30)) : (var_1_29 == ((signed long int) (128 + var_1_4))))) && (((var_1_54 + 0.75) <= var_1_24) ? (var_1_30 == ((signed long int) var_1_13)) : ((var_1_38 <= (var_1_34 / var_1_18)) ? (var_1_60 ? (var_1_30 == ((signed long int) (abs (var_1_38)))) : (var_1_30 == ((signed long int) (min (var_1_19 , (var_1_5 - var_1_18)))))) : (var_1_30 == ((signed long int) (var_1_13 + var_1_19)))))) && ((((var_1_39 + var_1_30) - var_1_18) >= (var_1_5 << var_1_14)) ? (var_1_31 == ((unsigned char) ((var_1_53 < 31.75f) || var_1_32))) : (var_1_31 == ((unsigned char) ((! 1) || var_1_33))))) && ((var_1_20 >= (var_1_24 - var_1_25)) ? (var_1_34 == ((unsigned char) (var_1_13 + (min ((min (var_1_27 , 64)) , (abs (10))))))) : (var_1_34 == ((unsigned char) (var_1_18 - var_1_13))))) && (((var_1_11 / 5) < (max ((last_1_var_1_35 + var_1_29) , var_1_28))) ? (var_1_35 == ((unsigned char) ((max (128 , (var_1_26 + var_1_36))) - (abs (var_1_37 - var_1_19))))) : (var_1_35 == ((unsigned char) ((abs (var_1_18)) - 2))))) && ((var_1_21 >= var_1_24) ? (var_1_38 == ((signed long int) ((min ((var_1_13 - var_1_58) , var_1_26)) + var_1_59))) : (var_1_38 == ((signed long int) (var_1_59 - var_1_18))))) && ((last_1_var_1_62 <= (32 * last_1_var_1_16)) ? (var_1_39 == ((signed short int) (var_1_18 - (var_1_40 - var_1_13)))) : 1)) && (var_1_60 ? (var_1_41 == ((signed long int) (last_1_var_1_41 - (var_1_9 + var_1_37)))) : (((0u >= 16u) || ((var_1_24 / var_1_20) >= var_1_25)) ? (var_1_41 == ((signed long int) var_1_22)) : 1))) && (((var_1_21 * var_1_54) < 63.75f) ? (((var_1_18 - (abs (var_1_27))) > (var_1_36 - (var_1_43 - var_1_58))) ? (var_1_42 == ((signed char) (min ((var_1_14 + var_1_19) , (var_1_13 - var_1_44))))) : 1) : ((((var_1_25 - var_1_24) / (min (var_1_21 , var_1_20))) != (var_1_45 - (max (var_1_46 , var_1_47)))) ? ((var_1_28 < var_1_11) ? (var_1_42 == ((signed char) (max ((min ((min (var_1_11 , var_1_14)) , var_1_12)) , (var_1_19 - (var_1_48 - var_1_49)))))) : (var_1_42 == ((signed char) (var_1_19 + (var_1_49 - (abs (var_1_14))))))) : (var_1_42 == ((signed char) (var_1_19 + (min ((-16 + 5) , 2)))))))) && (var_1_33 ? (var_1_50 == ((double) (var_1_51 + var_1_52))) : 1)) && (((var_1_63 || var_1_32) && var_1_63) ? (var_1_53 == ((float) (var_1_52 + 1000.2f))) : 1)) && ((((var_1_28 + var_1_44) % var_1_43) == -1000000) ? (var_1_54 == ((double) (max (var_1_51 , (var_1_55 - var_1_56))))) : (var_1_54 == ((double) (var_1_55 - var_1_56))))) && (((32 % var_1_18) >= (var_1_37 * (var_1_48 + 8))) ? (var_1_57 == ((unsigned short int) (max ((max (var_1_26 , var_1_30)) , ((var_1_44 + var_1_18) + (max (var_1_16 , var_1_4))))))) : ((var_1_62 < var_1_48) ? (var_1_57 == ((unsigned short int) var_1_62)) : (var_1_57 == ((unsigned short int) (abs (1 + (var_1_40 - var_1_19)))))))) && ((((max (var_1_59 , var_1_11)) * var_1_18) == var_1_62) ? (((min (var_1_18 , -5)) >= ((last_1_var_1_58 | var_1_5) | var_1_59)) ? (var_1_58 == ((unsigned short int) var_1_18)) : (var_1_58 == ((unsigned short int) var_1_39))) : 1)) && (var_1_59 == ((unsigned short int) (min (var_1_18 , var_1_4))))) && (var_1_60 == ((unsigned char) ((256 > var_1_39) && var_1_61)))) && (var_1_62 == ((unsigned long int) var_1_36))) && (var_1_63 == ((unsigned char) var_1_33))
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
