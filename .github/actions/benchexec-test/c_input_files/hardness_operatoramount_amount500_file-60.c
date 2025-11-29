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
void reach_error(void) { __assert_fail("0", "Req1_Prop1_Batch60Amount500.c", 13, "reach_error"); }
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
signed short int var_1_1 = 128;
signed short int var_1_7 = 0;
signed short int var_1_8 = 28520;
signed short int var_1_9 = 128;
signed short int var_1_10 = -10;
unsigned char var_1_11 = 0;
unsigned char var_1_12 = 100;
unsigned char var_1_13 = 1;
double var_1_14 = 255.25;
float var_1_15 = 64.75;
double var_1_16 = 128.25;
double var_1_17 = 0.0;
double var_1_18 = 256.375;
double var_1_19 = 15.8;
double var_1_20 = 99.65;
double var_1_21 = 0.0;
double var_1_22 = 8.75;
float var_1_23 = 10.2;
float var_1_24 = 9.25;
float var_1_25 = 499.6;
unsigned char var_1_26 = 32;
unsigned char var_1_27 = 0;
unsigned char var_1_28 = 1;
unsigned char var_1_29 = 0;
unsigned char var_1_30 = 0;
unsigned char var_1_31 = 0;
signed long int var_1_32 = 256;
signed short int var_1_33 = 1;
float var_1_34 = 1.625;
unsigned short int var_1_35 = 16;
signed char var_1_36 = 1;
signed char var_1_37 = -4;
signed char var_1_38 = -1;
signed char var_1_39 = 2;
unsigned long int var_1_40 = 8;
unsigned long int var_1_41 = 2;
unsigned long int var_1_42 = 1;
unsigned long int var_1_43 = 1460897009;
unsigned char var_1_44 = 8;
unsigned char var_1_46 = 128;
unsigned char var_1_47 = 32;
unsigned char var_1_48 = 5;
unsigned char var_1_49 = 0;
double var_1_50 = 256.49;
signed long int var_1_51 = 64;
double var_1_52 = 1000000000000000.6;
signed long int var_1_54 = 0;
signed long int var_1_55 = 1000000000;
signed short int var_1_57 = 32;
signed long int var_1_59 = 10;
signed short int var_1_60 = -25;
unsigned long int var_1_61 = 2265505711;
signed char var_1_62 = -1;
signed char var_1_63 = 4;
signed char var_1_64 = 16;
signed char var_1_65 = 8;
unsigned long int var_1_66 = 64;
unsigned char var_1_67 = 8;
signed char var_1_68 = 2;
signed long int var_1_69 = -2;
unsigned short int var_1_70 = 256;
unsigned short int var_1_71 = 55782;
double var_1_72 = 99999999.2;
unsigned char var_1_73 = 0;
unsigned char var_1_74 = 1;
unsigned char var_1_75 = 0;
unsigned char var_1_76 = 1;
unsigned long int var_1_77 = 64;
unsigned long int var_1_78 = 4147784183;
unsigned long int var_1_79 = 3879136688;
float var_1_80 = 127.6;
unsigned short int var_1_81 = 2;
unsigned short int var_1_82 = 16722;
unsigned short int var_1_83 = 256;
unsigned short int var_1_84 = 61841;
signed char var_1_85 = 1;
signed char var_1_86 = 4;
unsigned char var_1_87 = 1;
double var_1_88 = 99.25;
unsigned short int var_1_89 = 8;
unsigned char var_1_90 = 0;
unsigned char var_1_91 = 1;
unsigned char var_1_93 = 1;
signed short int var_1_94 = 8;
unsigned short int var_1_95 = 2;
unsigned long int var_1_96 = 0;
signed long int var_1_97 = 0;
signed long int var_1_98 = -1;
float var_1_99 = 128.125;
float var_1_100 = 15.5;
unsigned short int var_1_101 = 0;
double var_1_102 = 2.5;
double var_1_103 = 9999999999.6;
unsigned short int var_1_104 = 4;
float var_1_105 = 200.8;
float var_1_106 = 10.5;

// Calibration values

// Last'ed variables
signed short int last_1_var_1_33 = 1;
signed long int last_1_var_1_51 = 64;
signed long int last_1_var_1_54 = 0;
signed short int last_1_var_1_57 = 32;
unsigned long int last_1_var_1_66 = 64;
double last_1_var_1_72 = 99999999.2;
unsigned char last_1_var_1_75 = 0;
float last_1_var_1_80 = 127.6;
unsigned short int last_1_var_1_89 = 8;
unsigned char last_1_var_1_90 = 0;
unsigned char last_1_var_1_91 = 1;
signed long int last_1_var_1_98 = -1;
float last_1_var_1_105 = 200.8;

// Additional functions


void initially(void) {
}



void step(void) {
	// From: Req10Batch60Amount500
	if (((last_1_var_1_57 - var_1_28) < (last_1_var_1_54 & var_1_27)) && var_1_31) {
		var_1_34 = (var_1_24 - var_1_17);
	} else {
		var_1_34 = (var_1_19 + var_1_22);
	}


	// From: Req3Batch60Amount500
	signed long int stepLocal_3 = abs (var_1_9);
	unsigned char stepLocal_2 = var_1_12;
	if (stepLocal_2 < var_1_10) {
		if (last_1_var_1_80 >= ((last_1_var_1_72 + last_1_var_1_105) / var_1_15)) {
			var_1_14 = var_1_16;
		} else {
			if (var_1_8 == stepLocal_3) {
				var_1_14 = var_1_16;
			}
		}
	} else {
		var_1_14 = ((var_1_17 - 9.75) - 31.25);
	}


	// From: Req2Batch60Amount500
	signed long int stepLocal_1 = last_1_var_1_89 + (max (var_1_8 , var_1_9));
	if (((32 % var_1_12) * var_1_10) >= stepLocal_1) {
		var_1_11 = var_1_13;
	}


	// From: Req45Batch60Amount500
	if (var_1_11) {
		var_1_96 = var_1_43;
	} else {
		var_1_96 = var_1_46;
	}


	// From: Req11Batch60Amount500
	if (! var_1_13) {
		var_1_35 = (max ((min (var_1_28 , var_1_96)) , var_1_9));
	} else {
		var_1_35 = (abs (max (var_1_12 , var_1_9)));
	}


	// From: Req30Batch60Amount500
	if (128.125f <= (last_1_var_1_80 / var_1_15)) {
		var_1_74 = (! (last_1_var_1_91 || var_1_13));
	} else {
		if (last_1_var_1_90) {
			var_1_74 = var_1_31;
		} else {
			var_1_74 = (! (! var_1_13));
		}
	}


	// From: Req47Batch60Amount500
	if (var_1_74) {
		var_1_98 = last_1_var_1_98;
	} else {
		var_1_98 = -8;
	}


	// From: Req40Batch60Amount500
	if (last_1_var_1_75) {
		if (var_1_47 > var_1_41) {
			var_1_90 = (! var_1_13);
		}
	} else {
		var_1_90 = (((! var_1_31) && var_1_13) && var_1_76);
	}


	// From: Req33Batch60Amount500
	signed char stepLocal_26 = var_1_63;
	if (stepLocal_26 < var_1_9) {
		if (var_1_90) {
			var_1_80 = var_1_19;
		}
	} else {
		var_1_80 = var_1_17;
	}


	// From: Req31Batch60Amount500
	unsigned char stepLocal_21 = var_1_90;
	if (stepLocal_21 && var_1_74) {
		var_1_75 = (var_1_13 && var_1_76);
	} else {
		var_1_75 = var_1_76;
	}


	// From: Req9Batch60Amount500
	var_1_33 = (var_1_12 - (var_1_9 + last_1_var_1_33));


	// From: Req16Batch60Amount500
	unsigned char stepLocal_7 = var_1_28;
	if (stepLocal_7 == var_1_39) {
		var_1_50 = var_1_16;
	}


	// From: Req25Batch60Amount500
	if ((var_1_27 & var_1_39) <= var_1_49) {
		var_1_68 = (var_1_49 - var_1_47);
	} else {
		if ((var_1_46 + var_1_55) > (var_1_8 - var_1_9)) {
			var_1_68 = (min ((min (var_1_38 , (var_1_64 + var_1_65))) , (var_1_49 - var_1_63)));
		} else {
			var_1_68 = (min (((min (var_1_64 , var_1_49)) + var_1_65) , (abs (var_1_39 - var_1_47))));
		}
	}


	// From: Req42Batch60Amount500
	if (var_1_74) {
		var_1_93 = var_1_13;
	} else {
		var_1_93 = var_1_76;
	}


	// From: Req44Batch60Amount500
	var_1_95 = var_1_47;


	// From: Req46Batch60Amount500
	var_1_97 = var_1_95;


	// From: Req48Batch60Amount500
	var_1_99 = var_1_25;


	// From: Req49Batch60Amount500
	if (var_1_76) {
		var_1_100 = var_1_19;
	} else {
		var_1_100 = var_1_21;
	}


	// From: Req51Batch60Amount500
	if (var_1_75) {
		var_1_102 = var_1_103;
	}


	// From: Req52Batch60Amount500
	if (var_1_76) {
		var_1_104 = var_1_49;
	} else {
		var_1_104 = var_1_9;
	}


	// From: Req29Batch60Amount500
	if (var_1_16 != (var_1_34 / var_1_17)) {
		var_1_73 = ((! (var_1_75 && var_1_31)) && (! 0));
	}


	// From: Req37Batch60Amount500
	if (var_1_73) {
		var_1_87 = (var_1_63 + var_1_47);
	} else {
		var_1_87 = var_1_27;
	}


	// From: Req50Batch60Amount500
	if (var_1_93) {
		var_1_101 = var_1_49;
	} else {
		var_1_101 = var_1_87;
	}


	// From: Req13Batch60Amount500
	unsigned char stepLocal_6 = var_1_12;
	if (((var_1_15 + var_1_22) / 50.5f) < var_1_14) {
		if (! (var_1_15 >= var_1_25)) {
			if (var_1_50 > -0.06f) {
				var_1_40 = (var_1_41 + (var_1_29 + var_1_28));
			} else {
				var_1_40 = (5u + var_1_28);
			}
		} else {
			if ((25u ^ var_1_27) >= stepLocal_6) {
				if (var_1_31) {
					var_1_40 = ((var_1_29 + (max (var_1_9 , var_1_28))) + var_1_27);
				}
			} else {
				var_1_40 = (var_1_98 + var_1_9);
			}
		}
	} else {
		var_1_40 = (abs (var_1_28 + (abs (var_1_29))));
	}


	// From: Req34Batch60Amount500
	if (var_1_21 > (- var_1_25)) {
		var_1_81 = ((var_1_9 + var_1_40) + ((min (var_1_8 , var_1_82)) - var_1_63));
	}


	// From: Req19Batch60Amount500
	signed long int stepLocal_12 = (var_1_28 % var_1_47) / var_1_12;
	unsigned char stepLocal_11 = (16 > var_1_97) && var_1_90;
	signed long int stepLocal_10 = var_1_48 - var_1_28;
	if (var_1_22 >= var_1_14) {
		if (var_1_13 && stepLocal_11) {
			var_1_54 = ((max (var_1_27 , -32)) + var_1_81);
		} else {
			var_1_54 = ((var_1_49 - (var_1_55 - var_1_28)) + (var_1_12 + var_1_38));
		}
	} else {
		if (stepLocal_12 > last_1_var_1_54) {
			if (var_1_97 <= stepLocal_10) {
				var_1_54 = ((abs (abs (var_1_46))) + (max (var_1_49 , (var_1_48 - var_1_9))));
			} else {
				var_1_54 = (10 - var_1_55);
			}
		} else {
			var_1_54 = ((var_1_8 + var_1_49) - last_1_var_1_54);
		}
	}


	// From: Req43Batch60Amount500
	if (var_1_31) {
		var_1_94 = var_1_98;
	} else {
		var_1_94 = var_1_81;
	}


	// From: Req4Batch60Amount500
	if ((var_1_7 % var_1_12) >= var_1_10) {
		var_1_18 = (var_1_19 + var_1_20);
	} else {
		if (! var_1_13) {
			if (128.7 <= var_1_50) {
				var_1_18 = (max (var_1_17 , (var_1_20 + var_1_19)));
			} else {
				var_1_18 = ((var_1_21 + var_1_22) + (abs (var_1_20)));
			}
		} else {
			var_1_18 = 200.125;
		}
	}


	// From: Req21Batch60Amount500
	signed long int stepLocal_14 = max (var_1_87 , var_1_9);
	if (((var_1_61 - var_1_29) % var_1_8) > stepLocal_14) {
		if (var_1_75) {
			var_1_60 = var_1_96;
		}
	}


	// From: Req23Batch60Amount500
	signed long int stepLocal_18 = 4;
	if (stepLocal_18 <= (last_1_var_1_66 & var_1_7)) {
		var_1_66 = 256u;
	} else {
		var_1_66 = var_1_60;
	}


	// From: Req35Batch60Amount500
	if (var_1_22 < var_1_102) {
		var_1_83 = ((var_1_84 - var_1_39) - var_1_27);
	}


	// From: Req17Batch60Amount500
	signed char stepLocal_8 = var_1_37;
	if (var_1_50 == (var_1_21 / var_1_17)) {
		var_1_51 = (var_1_38 + last_1_var_1_51);
	} else {
		if (var_1_7 == stepLocal_8) {
			var_1_51 = (var_1_37 + (max ((max (var_1_39 , var_1_29)) , var_1_10)));
		} else {
			var_1_51 = (var_1_39 - (min (var_1_40 , var_1_101)));
		}
	}


	// From: Req41Batch60Amount500
	if (var_1_28 < var_1_94) {
		if (var_1_11 && var_1_74) {
			var_1_91 = var_1_31;
		} else {
			var_1_91 = var_1_13;
		}
	}


	// From: Req14Batch60Amount500
	if ((min (var_1_54 , var_1_12)) >= (min (var_1_97 , (var_1_38 - var_1_29)))) {
		if (var_1_7 >= var_1_37) {
			var_1_42 = ((min (var_1_9 , (var_1_43 - var_1_39))) + var_1_8);
		} else {
			var_1_42 = (min (var_1_43 , (min (1u , var_1_39))));
		}
	}


	// From: Req53Batch60Amount500
	unsigned short int stepLocal_32 = var_1_35;
	unsigned long int stepLocal_31 = var_1_96 | (- var_1_40);
	if (stepLocal_31 < var_1_55) {
		if ((abs (var_1_42)) >= stepLocal_32) {
			var_1_105 = (var_1_24 - (5.930652667988696E18f - var_1_106));
		} else {
			var_1_105 = var_1_24;
		}
	} else {
		var_1_105 = var_1_20;
	}


	// From: Req7Batch60Amount500
	unsigned char stepLocal_4 = (var_1_25 - var_1_17) <= var_1_20;
	if (stepLocal_4 && var_1_91) {
		var_1_30 = ((! var_1_13) || var_1_31);
	} else {
		var_1_30 = (! 0);
	}


	// From: Req8Batch60Amount500
	signed long int stepLocal_5 = -10 % 5;
	if (stepLocal_5 > var_1_28) {
		var_1_32 = (max (var_1_27 , ((var_1_29 + var_1_28) - var_1_8)));
	} else {
		var_1_32 = (var_1_29 - var_1_51);
	}


	// From: Req18Batch60Amount500
	unsigned long int stepLocal_9 = var_1_42;
	if (var_1_9 > stepLocal_9) {
		if (var_1_13) {
			if (var_1_99 > (var_1_17 - var_1_24)) {
				var_1_52 = (var_1_19 + var_1_21);
			}
		} else {
			var_1_52 = var_1_19;
		}
	} else {
		if (var_1_31) {
			var_1_52 = (min (var_1_16 , var_1_24));
		}
	}


	// From: Req22Batch60Amount500
	signed char stepLocal_17 = var_1_38;
	unsigned char stepLocal_16 = var_1_47;
	unsigned char stepLocal_15 = ! var_1_74;
	if (var_1_48 > stepLocal_16) {
		if ((var_1_31 || var_1_91) && stepLocal_15) {
			var_1_62 = ((var_1_49 + var_1_48) - var_1_47);
		}
	} else {
		if (stepLocal_17 >= var_1_41) {
			var_1_62 = (var_1_48 + ((var_1_63 - var_1_64) + (min (0 , var_1_65))));
		} else {
			var_1_62 = (var_1_39 - (max (var_1_49 , var_1_48)));
		}
	}


	// From: Req36Batch60Amount500
	unsigned long int stepLocal_27 = var_1_66 + (var_1_79 / -1);
	if (stepLocal_27 <= (var_1_32 + var_1_28)) {
		var_1_85 = ((min (var_1_86 , (min (var_1_48 , var_1_49)))) + 25);
	} else {
		if (var_1_16 >= var_1_14) {
			var_1_85 = (min (var_1_38 , var_1_65));
		} else {
			var_1_85 = (max (-64 , (abs (var_1_86))));
		}
	}


	// From: Req38Batch60Amount500
	unsigned long int stepLocal_29 = (var_1_47 << var_1_97) + 256u;
	signed long int stepLocal_28 = var_1_51;
	if (stepLocal_29 >= (var_1_78 - var_1_12)) {
		if (var_1_12 <= stepLocal_28) {
			var_1_88 = (var_1_21 + var_1_22);
		} else {
			var_1_88 = (abs (max ((min (var_1_21 , var_1_20)) , var_1_22)));
		}
	} else {
		var_1_88 = 7.25;
	}


	// From: Req28Batch60Amount500
	if (var_1_91) {
		var_1_72 = var_1_21;
	} else {
		var_1_72 = (var_1_24 - 5.8);
	}


	// From: Req39Batch60Amount500
	unsigned char stepLocal_30 = var_1_27;
	if (var_1_100 > var_1_72) {
		var_1_89 = (5 + (min (var_1_63 , var_1_28)));
	} else {
		if (stepLocal_30 > (var_1_97 / var_1_47)) {
			var_1_89 = (abs (var_1_28));
		}
	}


	// From: Req1Batch60Amount500
	unsigned char stepLocal_0 = var_1_88 <= (max (var_1_52 , var_1_18));
	if (var_1_90) {
		if (var_1_93 && stepLocal_0) {
			if (var_1_88 >= var_1_18) {
				var_1_1 = (var_1_7 - (var_1_8 - var_1_9));
			} else {
				var_1_1 = ((max (var_1_9 , var_1_10)) + -1);
			}
		} else {
			var_1_1 = (var_1_10 + var_1_9);
		}
	}


	// From: Req5Batch60Amount500
	if (var_1_11) {
		if (var_1_88 >= var_1_22) {
			var_1_23 = (var_1_17 - var_1_24);
		}
	} else {
		if ((- var_1_99) < var_1_88) {
			var_1_23 = ((max (var_1_25 , var_1_17)) - var_1_24);
		} else {
			var_1_23 = 5.2f;
		}
	}


	// From: Req6Batch60Amount500
	if (var_1_88 <= var_1_102) {
		if (var_1_11) {
			var_1_26 = (var_1_27 + (max (var_1_28 , var_1_29)));
		}
	} else {
		var_1_26 = var_1_27;
	}


	// From: Req15Batch60Amount500
	if (var_1_91) {
		var_1_44 = 25;
	} else {
		if ((min (var_1_37 , var_1_89)) > ((max (var_1_8 , 5)) - var_1_12)) {
			var_1_44 = (var_1_46 - ((var_1_47 - 2) + (min (var_1_48 , var_1_49))));
		}
	}


	// From: Req24Batch60Amount500
	unsigned char stepLocal_19 = var_1_30;
	if ((var_1_21 >= var_1_88) || stepLocal_19) {
		if ((var_1_50 + var_1_52) <= 100.25) {
			var_1_67 = var_1_27;
		}
	}


	// From: Req27Batch60Amount500
	if (var_1_25 <= (- (var_1_99 * 100.5f))) {
		if ((- var_1_72) <= (var_1_14 * var_1_18)) {
			var_1_70 = (var_1_71 - (var_1_8 - var_1_48));
		} else {
			var_1_70 = (min ((max ((var_1_8 + var_1_48) , var_1_27)) , var_1_47));
		}
	} else {
		var_1_70 = var_1_27;
	}


	// From: Req32Batch60Amount500
	unsigned long int stepLocal_25 = var_1_51 & var_1_96;
	unsigned char stepLocal_24 = var_1_74;
	signed long int stepLocal_23 = var_1_97;
	signed long int stepLocal_22 = var_1_51;
	if ((var_1_96 / var_1_46) == stepLocal_23) {
		if (var_1_12 == stepLocal_25) {
			var_1_77 = var_1_29;
		} else {
			var_1_77 = (var_1_70 + ((abs (var_1_43)) - (min (var_1_9 , var_1_48))));
		}
	} else {
		if (((max (var_1_42 , var_1_48)) * var_1_81) == stepLocal_22) {
			if (stepLocal_24 || (var_1_12 >= var_1_40)) {
				var_1_77 = (((abs (var_1_43)) - var_1_9) + (min (var_1_12 , var_1_35)));
			} else {
				var_1_77 = (var_1_78 - var_1_81);
			}
		} else {
			var_1_77 = ((var_1_79 - var_1_71) - (var_1_39 + var_1_28));
		}
	}


	// From: Req26Batch60Amount500
	signed long int stepLocal_20 = var_1_47 & var_1_87;
	if ((min (var_1_66 , (var_1_59 + var_1_55))) == stepLocal_20) {
		var_1_69 = (max (var_1_83 , ((var_1_8 - var_1_48) + var_1_70)));
	}


	// From: Req20Batch60Amount500
	signed long int stepLocal_13 = (abs (var_1_38)) % (max (var_1_8 , var_1_55));
	if (((var_1_95 ^ var_1_77) * (var_1_97 % var_1_46)) >= stepLocal_13) {
		var_1_57 = var_1_9;
	}


	// From: Req12Batch60Amount500
	if ((var_1_57 + var_1_8) < (var_1_10 & var_1_12)) {
		var_1_36 = (max (var_1_37 , (var_1_38 - var_1_39)));
	} else {
		var_1_36 = (max ((abs (var_1_38)) , (var_1_39 - 5)));
	}
}



void updateVariables(void) {
	var_1_7 = __VERIFIER_nondet_short();
	assume_abort_if_not(var_1_7 >= -1);
	assume_abort_if_not(var_1_7 <= 32766);
	var_1_8 = __VERIFIER_nondet_short();
	assume_abort_if_not(var_1_8 >= 16383);
	assume_abort_if_not(var_1_8 <= 32766);
	var_1_9 = __VERIFIER_nondet_short();
	assume_abort_if_not(var_1_9 >= 0);
	assume_abort_if_not(var_1_9 <= 16383);
	var_1_10 = __VERIFIER_nondet_short();
	assume_abort_if_not(var_1_10 >= -16383);
	assume_abort_if_not(var_1_10 <= 16383);
	var_1_12 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_12 >= 0);
	assume_abort_if_not(var_1_12 <= 255);
	assume_abort_if_not(var_1_12 != 0);
	var_1_13 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_13 >= 1);
	assume_abort_if_not(var_1_13 <= 1);
	var_1_15 = __VERIFIER_nondet_float();
	assume_abort_if_not((var_1_15 >= -922337.2036854776000e+13F && var_1_15 <= -1.0e-20F) || (var_1_15 <= 9223372.036854776000e+12F && var_1_15 >= 1.0e-20F ));
	assume_abort_if_not(var_1_15 != 0.0F);
	var_1_16 = __VERIFIER_nondet_double();
	assume_abort_if_not((var_1_16 >= -922337.2036854766000e+13F && var_1_16 <= -1.0e-20F) || (var_1_16 <= 9223372.036854766000e+12F && var_1_16 >= 1.0e-20F ));
	var_1_17 = __VERIFIER_nondet_double();
	assume_abort_if_not((var_1_17 >= 4611686.018427383000e+12F && var_1_17 <= -1.0e-20F) || (var_1_17 <= 9223372.036854766000e+12F && var_1_17 >= 1.0e-20F ));
	var_1_19 = __VERIFIER_nondet_double();
	assume_abort_if_not((var_1_19 >= -461168.6018427383000e+13F && var_1_19 <= -1.0e-20F) || (var_1_19 <= 4611686.018427383000e+12F && var_1_19 >= 1.0e-20F ));
	var_1_20 = __VERIFIER_nondet_double();
	assume_abort_if_not((var_1_20 >= -461168.6018427383000e+13F && var_1_20 <= -1.0e-20F) || (var_1_20 <= 4611686.018427383000e+12F && var_1_20 >= 1.0e-20F ));
	var_1_21 = __VERIFIER_nondet_double();
	assume_abort_if_not((var_1_21 >= -230584.3009213691400e+13F && var_1_21 <= -1.0e-20F) || (var_1_21 <= 2305843.009213691400e+12F && var_1_21 >= 1.0e-20F ));
	var_1_22 = __VERIFIER_nondet_double();
	assume_abort_if_not((var_1_22 >= -230584.3009213691400e+13F && var_1_22 <= -1.0e-20F) || (var_1_22 <= 2305843.009213691400e+12F && var_1_22 >= 1.0e-20F ));
	var_1_24 = __VERIFIER_nondet_float();
	assume_abort_if_not((var_1_24 >= 0.0F && var_1_24 <= -1.0e-20F) || (var_1_24 <= 9223372.036854766000e+12F && var_1_24 >= 1.0e-20F ));
	var_1_25 = __VERIFIER_nondet_float();
	assume_abort_if_not((var_1_25 >= 0.0F && var_1_25 <= -1.0e-20F) || (var_1_25 <= 9223372.036854766000e+12F && var_1_25 >= 1.0e-20F ));
	var_1_27 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_27 >= 0);
	assume_abort_if_not(var_1_27 <= 127);
	var_1_28 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_28 >= 0);
	assume_abort_if_not(var_1_28 <= 127);
	var_1_29 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_29 >= 0);
	assume_abort_if_not(var_1_29 <= 127);
	var_1_31 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_31 >= 0);
	assume_abort_if_not(var_1_31 <= 0);
	var_1_37 = __VERIFIER_nondet_char();
	assume_abort_if_not(var_1_37 >= -127);
	assume_abort_if_not(var_1_37 <= 126);
	var_1_38 = __VERIFIER_nondet_char();
	assume_abort_if_not(var_1_38 >= -1);
	assume_abort_if_not(var_1_38 <= 126);
	var_1_39 = __VERIFIER_nondet_char();
	assume_abort_if_not(var_1_39 >= 0);
	assume_abort_if_not(var_1_39 <= 126);
	var_1_41 = __VERIFIER_nondet_ulong();
	assume_abort_if_not(var_1_41 >= 0);
	assume_abort_if_not(var_1_41 <= 2147483647);
	var_1_43 = __VERIFIER_nondet_ulong();
	assume_abort_if_not(var_1_43 >= 1073741823);
	assume_abort_if_not(var_1_43 <= 2147483647);
	var_1_46 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_46 >= 127);
	assume_abort_if_not(var_1_46 <= 254);
	var_1_47 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_47 >= 32);
	assume_abort_if_not(var_1_47 <= 64);
	var_1_48 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_48 >= 0);
	assume_abort_if_not(var_1_48 <= 63);
	var_1_49 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_49 >= 0);
	assume_abort_if_not(var_1_49 <= 63);
	var_1_55 = __VERIFIER_nondet_long();
	assume_abort_if_not(var_1_55 >= 536870911);
	assume_abort_if_not(var_1_55 <= 1073741823);
	var_1_59 = __VERIFIER_nondet_long();
	assume_abort_if_not(var_1_59 >= -1);
	assume_abort_if_not(var_1_59 <= 2147483647);
	var_1_61 = __VERIFIER_nondet_ulong();
	assume_abort_if_not(var_1_61 >= 2147483647);
	assume_abort_if_not(var_1_61 <= 4294967295);
	var_1_63 = __VERIFIER_nondet_char();
	assume_abort_if_not(var_1_63 >= 0);
	assume_abort_if_not(var_1_63 <= 32);
	var_1_64 = __VERIFIER_nondet_char();
	assume_abort_if_not(var_1_64 >= 0);
	assume_abort_if_not(var_1_64 <= 31);
	var_1_65 = __VERIFIER_nondet_char();
	assume_abort_if_not(var_1_65 >= -31);
	assume_abort_if_not(var_1_65 <= 31);
	var_1_71 = __VERIFIER_nondet_ushort();
	assume_abort_if_not(var_1_71 >= 32767);
	assume_abort_if_not(var_1_71 <= 65534);
	var_1_76 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_76 >= 1);
	assume_abort_if_not(var_1_76 <= 1);
	var_1_78 = __VERIFIER_nondet_ulong();
	assume_abort_if_not(var_1_78 >= 2147483647);
	assume_abort_if_not(var_1_78 <= 4294967294);
	var_1_79 = __VERIFIER_nondet_ulong();
	assume_abort_if_not(var_1_79 >= 3221225470);
	assume_abort_if_not(var_1_79 <= 4294967294);
	var_1_82 = __VERIFIER_nondet_ushort();
	assume_abort_if_not(var_1_82 >= 16383);
	assume_abort_if_not(var_1_82 <= 32767);
	var_1_84 = __VERIFIER_nondet_ushort();
	assume_abort_if_not(var_1_84 >= 49150);
	assume_abort_if_not(var_1_84 <= 65534);
	var_1_86 = __VERIFIER_nondet_char();
	assume_abort_if_not(var_1_86 >= -63);
	assume_abort_if_not(var_1_86 <= 63);
	var_1_103 = __VERIFIER_nondet_double();
	assume_abort_if_not((var_1_103 >= -922337.2036854766000e+13F && var_1_103 <= -1.0e-20F) || (var_1_103 <= 9223372.036854766000e+12F && var_1_103 >= 1.0e-20F ));
	var_1_106 = __VERIFIER_nondet_float();
	assume_abort_if_not((var_1_106 >= 0.0F && var_1_106 <= -1.0e-20F) || (var_1_106 <= 4611686.018427383000e+12F && var_1_106 >= 1.0e-20F ));
}



void updateLastVariables(void) {
	last_1_var_1_33 = var_1_33;
	last_1_var_1_51 = var_1_51;
	last_1_var_1_54 = var_1_54;
	last_1_var_1_57 = var_1_57;
	last_1_var_1_66 = var_1_66;
	last_1_var_1_72 = var_1_72;
	last_1_var_1_75 = var_1_75;
	last_1_var_1_80 = var_1_80;
	last_1_var_1_89 = var_1_89;
	last_1_var_1_90 = var_1_90;
	last_1_var_1_91 = var_1_91;
	last_1_var_1_98 = var_1_98;
	last_1_var_1_105 = var_1_105;
}

int property(void) {
	return ((((((((((((((((((((((((((((((((((((((((((((((((((((var_1_90 ? ((var_1_93 && (var_1_88 <= (max (var_1_52 , var_1_18)))) ? ((var_1_88 >= var_1_18) ? (var_1_1 == ((signed short int) (var_1_7 - (var_1_8 - var_1_9)))) : (var_1_1 == ((signed short int) ((max (var_1_9 , var_1_10)) + -1)))) : (var_1_1 == ((signed short int) (var_1_10 + var_1_9)))) : 1) && ((((32 % var_1_12) * var_1_10) >= (last_1_var_1_89 + (max (var_1_8 , var_1_9)))) ? (var_1_11 == ((unsigned char) var_1_13)) : 1)) && ((var_1_12 < var_1_10) ? ((last_1_var_1_80 >= ((last_1_var_1_72 + last_1_var_1_105) / var_1_15)) ? (var_1_14 == ((double) var_1_16)) : ((var_1_8 == (abs (var_1_9))) ? (var_1_14 == ((double) var_1_16)) : 1)) : (var_1_14 == ((double) ((var_1_17 - 9.75) - 31.25))))) && (((var_1_7 % var_1_12) >= var_1_10) ? (var_1_18 == ((double) (var_1_19 + var_1_20))) : ((! var_1_13) ? ((128.7 <= var_1_50) ? (var_1_18 == ((double) (max (var_1_17 , (var_1_20 + var_1_19))))) : (var_1_18 == ((double) ((var_1_21 + var_1_22) + (abs (var_1_20)))))) : (var_1_18 == ((double) 200.125))))) && (var_1_11 ? ((var_1_88 >= var_1_22) ? (var_1_23 == ((float) (var_1_17 - var_1_24))) : 1) : (((- var_1_99) < var_1_88) ? (var_1_23 == ((float) ((max (var_1_25 , var_1_17)) - var_1_24))) : (var_1_23 == ((float) 5.2f))))) && ((var_1_88 <= var_1_102) ? (var_1_11 ? (var_1_26 == ((unsigned char) (var_1_27 + (max (var_1_28 , var_1_29))))) : 1) : (var_1_26 == ((unsigned char) var_1_27)))) && ((((var_1_25 - var_1_17) <= var_1_20) && var_1_91) ? (var_1_30 == ((unsigned char) ((! var_1_13) || var_1_31))) : (var_1_30 == ((unsigned char) (! 0))))) && (((-10 % 5) > var_1_28) ? (var_1_32 == ((signed long int) (max (var_1_27 , ((var_1_29 + var_1_28) - var_1_8))))) : (var_1_32 == ((signed long int) (var_1_29 - var_1_51))))) && (var_1_33 == ((signed short int) (var_1_12 - (var_1_9 + last_1_var_1_33))))) && ((((last_1_var_1_57 - var_1_28) < (last_1_var_1_54 & var_1_27)) && var_1_31) ? (var_1_34 == ((float) (var_1_24 - var_1_17))) : (var_1_34 == ((float) (var_1_19 + var_1_22))))) && ((! var_1_13) ? (var_1_35 == ((unsigned short int) (max ((min (var_1_28 , var_1_96)) , var_1_9)))) : (var_1_35 == ((unsigned short int) (abs (max (var_1_12 , var_1_9))))))) && (((var_1_57 + var_1_8) < (var_1_10 & var_1_12)) ? (var_1_36 == ((signed char) (max (var_1_37 , (var_1_38 - var_1_39))))) : (var_1_36 == ((signed char) (max ((abs (var_1_38)) , (var_1_39 - 5))))))) && ((((var_1_15 + var_1_22) / 50.5f) < var_1_14) ? ((! (var_1_15 >= var_1_25)) ? ((var_1_50 > -0.06f) ? (var_1_40 == ((unsigned long int) (var_1_41 + (var_1_29 + var_1_28)))) : (var_1_40 == ((unsigned long int) (5u + var_1_28)))) : (((25u ^ var_1_27) >= var_1_12) ? (var_1_31 ? (var_1_40 == ((unsigned long int) ((var_1_29 + (max (var_1_9 , var_1_28))) + var_1_27))) : 1) : (var_1_40 == ((unsigned long int) (var_1_98 + var_1_9))))) : (var_1_40 == ((unsigned long int) (abs (var_1_28 + (abs (var_1_29)))))))) && (((min (var_1_54 , var_1_12)) >= (min (var_1_97 , (var_1_38 - var_1_29)))) ? ((var_1_7 >= var_1_37) ? (var_1_42 == ((unsigned long int) ((min (var_1_9 , (var_1_43 - var_1_39))) + var_1_8))) : (var_1_42 == ((unsigned long int) (min (var_1_43 , (min (1u , var_1_39))))))) : 1)) && (var_1_91 ? (var_1_44 == ((unsigned char) 25)) : (((min (var_1_37 , var_1_89)) > ((max (var_1_8 , 5)) - var_1_12)) ? (var_1_44 == ((unsigned char) (var_1_46 - ((var_1_47 - 2) + (min (var_1_48 , var_1_49)))))) : 1))) && ((var_1_28 == var_1_39) ? (var_1_50 == ((double) var_1_16)) : 1)) && ((var_1_50 == (var_1_21 / var_1_17)) ? (var_1_51 == ((signed long int) (var_1_38 + last_1_var_1_51))) : ((var_1_7 == var_1_37) ? (var_1_51 == ((signed long int) (var_1_37 + (max ((max (var_1_39 , var_1_29)) , var_1_10))))) : (var_1_51 == ((signed long int) (var_1_39 - (min (var_1_40 , var_1_101)))))))) && ((var_1_9 > var_1_42) ? (var_1_13 ? ((var_1_99 > (var_1_17 - var_1_24)) ? (var_1_52 == ((double) (var_1_19 + var_1_21))) : 1) : (var_1_52 == ((double) var_1_19))) : (var_1_31 ? (var_1_52 == ((double) (min (var_1_16 , var_1_24)))) : 1))) && ((var_1_22 >= var_1_14) ? ((var_1_13 && ((16 > var_1_97) && var_1_90)) ? (var_1_54 == ((signed long int) ((max (var_1_27 , -32)) + var_1_81))) : (var_1_54 == ((signed long int) ((var_1_49 - (var_1_55 - var_1_28)) + (var_1_12 + var_1_38))))) : ((((var_1_28 % var_1_47) / var_1_12) > last_1_var_1_54) ? ((var_1_97 <= (var_1_48 - var_1_28)) ? (var_1_54 == ((signed long int) ((abs (abs (var_1_46))) + (max (var_1_49 , (var_1_48 - var_1_9)))))) : (var_1_54 == ((signed long int) (10 - var_1_55)))) : (var_1_54 == ((signed long int) ((var_1_8 + var_1_49) - last_1_var_1_54)))))) && ((((var_1_95 ^ var_1_77) * (var_1_97 % var_1_46)) >= ((abs (var_1_38)) % (max (var_1_8 , var_1_55)))) ? (var_1_57 == ((signed short int) var_1_9)) : 1)) && ((((var_1_61 - var_1_29) % var_1_8) > (max (var_1_87 , var_1_9))) ? (var_1_75 ? (var_1_60 == ((signed short int) var_1_96)) : 1) : 1)) && ((var_1_48 > var_1_47) ? (((var_1_31 || var_1_91) && (! var_1_74)) ? (var_1_62 == ((signed char) ((var_1_49 + var_1_48) - var_1_47))) : 1) : ((var_1_38 >= var_1_41) ? (var_1_62 == ((signed char) (var_1_48 + ((var_1_63 - var_1_64) + (min (0 , var_1_65)))))) : (var_1_62 == ((signed char) (var_1_39 - (max (var_1_49 , var_1_48)))))))) && ((4 <= (last_1_var_1_66 & var_1_7)) ? (var_1_66 == ((unsigned long int) 256u)) : (var_1_66 == ((unsigned long int) var_1_60)))) && (((var_1_21 >= var_1_88) || var_1_30) ? (((var_1_50 + var_1_52) <= 100.25) ? (var_1_67 == ((unsigned char) var_1_27)) : 1) : 1)) && (((var_1_27 & var_1_39) <= var_1_49) ? (var_1_68 == ((signed char) (var_1_49 - var_1_47))) : (((var_1_46 + var_1_55) > (var_1_8 - var_1_9)) ? (var_1_68 == ((signed char) (min ((min (var_1_38 , (var_1_64 + var_1_65))) , (var_1_49 - var_1_63))))) : (var_1_68 == ((signed char) (min (((min (var_1_64 , var_1_49)) + var_1_65) , (abs (var_1_39 - var_1_47))))))))) && (((min (var_1_66 , (var_1_59 + var_1_55))) == (var_1_47 & var_1_87)) ? (var_1_69 == ((signed long int) (max (var_1_83 , ((var_1_8 - var_1_48) + var_1_70))))) : 1)) && ((var_1_25 <= (- (var_1_99 * 100.5f))) ? (((- var_1_72) <= (var_1_14 * var_1_18)) ? (var_1_70 == ((unsigned short int) (var_1_71 - (var_1_8 - var_1_48)))) : (var_1_70 == ((unsigned short int) (min ((max ((var_1_8 + var_1_48) , var_1_27)) , var_1_47))))) : (var_1_70 == ((unsigned short int) var_1_27)))) && (var_1_91 ? (var_1_72 == ((double) var_1_21)) : (var_1_72 == ((double) (var_1_24 - 5.8))))) && ((var_1_16 != (var_1_34 / var_1_17)) ? (var_1_73 == ((unsigned char) ((! (var_1_75 && var_1_31)) && (! 0)))) : 1)) && ((128.125f <= (last_1_var_1_80 / var_1_15)) ? (var_1_74 == ((unsigned char) (! (last_1_var_1_91 || var_1_13)))) : (last_1_var_1_90 ? (var_1_74 == ((unsigned char) var_1_31)) : (var_1_74 == ((unsigned char) (! (! var_1_13))))))) && ((var_1_90 && var_1_74) ? (var_1_75 == ((unsigned char) (var_1_13 && var_1_76))) : (var_1_75 == ((unsigned char) var_1_76)))) && (((var_1_96 / var_1_46) == var_1_97) ? ((var_1_12 == (var_1_51 & var_1_96)) ? (var_1_77 == ((unsigned long int) var_1_29)) : (var_1_77 == ((unsigned long int) (var_1_70 + ((abs (var_1_43)) - (min (var_1_9 , var_1_48))))))) : ((((max (var_1_42 , var_1_48)) * var_1_81) == var_1_51) ? ((var_1_74 || (var_1_12 >= var_1_40)) ? (var_1_77 == ((unsigned long int) (((abs (var_1_43)) - var_1_9) + (min (var_1_12 , var_1_35))))) : (var_1_77 == ((unsigned long int) (var_1_78 - var_1_81)))) : (var_1_77 == ((unsigned long int) ((var_1_79 - var_1_71) - (var_1_39 + var_1_28))))))) && ((var_1_63 < var_1_9) ? (var_1_90 ? (var_1_80 == ((float) var_1_19)) : 1) : (var_1_80 == ((float) var_1_17)))) && ((var_1_21 > (- var_1_25)) ? (var_1_81 == ((unsigned short int) ((var_1_9 + var_1_40) + ((min (var_1_8 , var_1_82)) - var_1_63)))) : 1)) && ((var_1_22 < var_1_102) ? (var_1_83 == ((unsigned short int) ((var_1_84 - var_1_39) - var_1_27))) : 1)) && (((var_1_66 + (var_1_79 / -1)) <= (var_1_32 + var_1_28)) ? (var_1_85 == ((signed char) ((min (var_1_86 , (min (var_1_48 , var_1_49)))) + 25))) : ((var_1_16 >= var_1_14) ? (var_1_85 == ((signed char) (min (var_1_38 , var_1_65)))) : (var_1_85 == ((signed char) (max (-64 , (abs (var_1_86))))))))) && (var_1_73 ? (var_1_87 == ((unsigned char) (var_1_63 + var_1_47))) : (var_1_87 == ((unsigned char) var_1_27)))) && ((((var_1_47 << var_1_97) + 256u) >= (var_1_78 - var_1_12)) ? ((var_1_12 <= var_1_51) ? (var_1_88 == ((double) (var_1_21 + var_1_22))) : (var_1_88 == ((double) (abs (max ((min (var_1_21 , var_1_20)) , var_1_22)))))) : (var_1_88 == ((double) 7.25)))) && ((var_1_100 > var_1_72) ? (var_1_89 == ((unsigned short int) (5 + (min (var_1_63 , var_1_28))))) : ((var_1_27 > (var_1_97 / var_1_47)) ? (var_1_89 == ((unsigned short int) (abs (var_1_28)))) : 1))) && (last_1_var_1_75 ? ((var_1_47 > var_1_41) ? (var_1_90 == ((unsigned char) (! var_1_13))) : 1) : (var_1_90 == ((unsigned char) (((! var_1_31) && var_1_13) && var_1_76))))) && ((var_1_28 < var_1_94) ? ((var_1_11 && var_1_74) ? (var_1_91 == ((unsigned char) var_1_31)) : (var_1_91 == ((unsigned char) var_1_13))) : 1)) && (var_1_74 ? (var_1_93 == ((unsigned char) var_1_13)) : (var_1_93 == ((unsigned char) var_1_76)))) && (var_1_31 ? (var_1_94 == ((signed short int) var_1_98)) : (var_1_94 == ((signed short int) var_1_81)))) && (var_1_95 == ((unsigned short int) var_1_47))) && (var_1_11 ? (var_1_96 == ((unsigned long int) var_1_43)) : (var_1_96 == ((unsigned long int) var_1_46)))) && (var_1_97 == ((signed long int) var_1_95))) && (var_1_74 ? (var_1_98 == ((signed long int) last_1_var_1_98)) : (var_1_98 == ((signed long int) -8)))) && (var_1_99 == ((float) var_1_25))) && (var_1_76 ? (var_1_100 == ((float) var_1_19)) : (var_1_100 == ((float) var_1_21)))) && (var_1_93 ? (var_1_101 == ((unsigned short int) var_1_49)) : (var_1_101 == ((unsigned short int) var_1_87)))) && (var_1_75 ? (var_1_102 == ((double) var_1_103)) : 1)) && (var_1_76 ? (var_1_104 == ((unsigned short int) var_1_49)) : (var_1_104 == ((unsigned short int) var_1_9)))) && (((var_1_96 | (- var_1_40)) < var_1_55) ? (((abs (var_1_42)) >= var_1_35) ? (var_1_105 == ((float) (var_1_24 - (5.930652667988696E18f - var_1_106)))) : (var_1_105 == ((float) var_1_24))) : (var_1_105 == ((float) var_1_20)))
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
