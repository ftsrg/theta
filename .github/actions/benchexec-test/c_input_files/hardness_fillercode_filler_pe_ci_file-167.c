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
void reach_error(void) { __assert_fail("0", "Req1_Prop1_Batch167Filler_PE_CI.c", 13, "reach_error"); }
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
float var_1_1 = 255.5;
unsigned char var_1_2 = 1;
unsigned long int var_1_3 = 10000000;
unsigned long int var_1_4 = 5;
unsigned long int var_1_5 = 0;
float var_1_6 = 31.8;
float var_1_7 = 0.19999999999999996;
float var_1_8 = 128.75;
float var_1_9 = 63.6;
float var_1_10 = 9.5;
double var_1_11 = 7.6;
float var_1_12 = 99.5;
signed char var_1_13 = -10;
unsigned char var_1_14 = 0;
unsigned char var_1_15 = 1;
signed char var_1_16 = -16;
signed short int var_1_17 = 1;
signed long int var_1_18 = 16;
signed short int var_1_19 = 25;
unsigned short int var_1_20 = 64;
unsigned short int var_1_21 = 128;
unsigned short int var_1_22 = 2;
unsigned short int var_1_23 = 10;
signed char var_1_24 = 8;
float var_1_25 = 31.8;
signed char var_1_26 = -5;
unsigned char var_1_27 = 0;
unsigned char var_1_28 = 0;
unsigned char var_1_29 = 0;
unsigned char var_1_30 = 0;
double var_1_31 = 31.8;
double var_1_33 = 63.8;
signed long int var_1_34 = -128;
signed long int var_1_35 = -100;
signed long int var_1_36 = -128;
signed long int var_1_37 = -10;
unsigned short int var_1_38 = 64;
unsigned char var_1_40 = 0;
unsigned long int var_1_42 = 128;
unsigned char var_1_43 = 100;
float var_1_44 = 2.2;
float var_1_45 = 127.225;
unsigned char var_1_46 = 50;
double var_1_47 = 500.625;
double var_1_48 = 63.5;
unsigned char var_1_49 = 1;
unsigned char var_1_50 = 100;
signed short int var_1_51 = -16;
unsigned long int var_1_52 = 3203620775;
unsigned long int var_1_53 = 3508692917;

// Calibration values

// Last'ed variables

// Additional functions


void initially(void) {
}



void step(void) {
	// From: Req1Batch167Filler_PE_CI
	unsigned long int stepLocal_0 = var_1_3;
	/* 821L, 34L, 248L, 271L) */ if (/* 804L, 7L, 8L, 249L, 272L) */ ((stepLocal_0) == (/* 803L, 6L, 10L, 251L, 274L) */ (max (/* 803L, 6L, 10L, 251L, 274L) */ (var_1_4) , (var_1_5)))))) {
		/* 816L, 29L, 254L, 277L) */ var_1_1 = (
			/* 815L, 28L, 257L, 280L) */ ((
				/* 813L, 26L, 258L, 281L) */ ((
					/* 809L, 22L, 259L, 282L) */ ((
						var_1_6
					) + (
						var_1_7
					))
				) + (
					/* 812L, 25L, 262L, 285L) */ (min (
						/* 812L, 25L, 262L, 285L) */ (
							var_1_8
						) , (
							var_1_9
						)
					))
				))
			) - (
				var_1_10
			))
		);
	} else {
		/* 820L, 33L, 266L, 289L) */ var_1_1 = (
			8.2f
		);
	}


	// From: Req2Batch167Filler_PE_CI
	/* 825L, 71L, 340L, 359L) */ if (/* 826L, 46L, 47L, 341L, 360L) */ ((var_1_10) > (/* 828L, 45L, 49L, 343L, 362L) */ ((var_1_7) * (/* 830L, 44L, 51L, 345L, 364L) */ ((var_1_6) / (var_1_12))))))) {
		/* 833L, 66L, 348L, 367L) */ var_1_11 = (
			/* 836L, 65L, 351L, 370L) */ ((
				var_1_7
			) - (
				var_1_9
			))
		);
	} else {
		/* 839L, 70L, 354L, 373L) */ var_1_11 = (
			var_1_8
		);
	}


	// From: Req3Batch167Filler_PE_CI
	unsigned char stepLocal_1 = var_1_15;
	/* 855L, 96L, 438L, 449L) */ if (/* 850L, 81L, 82L, 439L, 450L) */ ((/* 849L, 79L, 83L, 440L, 451L) */ ((var_1_2) && (var_1_14))) && (stepLocal_1))) {
		/* 854L, 95L, 444L, 455L) */ var_1_13 = (
			var_1_16
		);
	}


	// From: Req5Batch167Filler_PE_CI
	/* 883L, 149L, 559L, 571L) */ var_1_20 = (
		/* 886L, 148L, 562L, 574L) */ ((
			/* 887L, 144L, 563L, 575L) */ ((
				var_1_21
			) + (
				16
			))
		) + (
			/* 890L, 147L, 566L, 578L) */ ((
				var_1_22
			) + (
				var_1_23
			))
		))
	);


	// From: Req6Batch167Filler_PE_CI
	/* 895L, 214L, 607L, 639L) */ if (/* 896L, 161L, 162L, 608L, 640L) */ ((/* 897L, 159L, 163L, 609L, 641L) */ (min (/* 897L, 159L, 163L, 609L, 641L) */ (var_1_1) , (/* 899L, 158L, 165L, 611L, 643L) */ (- (var_1_9)))))) > (var_1_8))) {
		/* 902L, 208L, 614L, 646L) */ if (/* 903L, 181L, 182L, 615L, 647L) */ ((/* 904L, 179L, 183L, 616L, 648L) */ ((/* 905L, 175L, 184L, 617L, 649L) */ (abs (var_1_7))) / (/* 907L, 178L, 186L, 619L, 651L) */ (max (/* 907L, 178L, 186L, 619L, 651L) */ (var_1_12) , (var_1_25)))))) < (var_1_11))) {
			/* 911L, 203L, 623L, 655L) */ var_1_24 = (
				/* 914L, 202L, 626L, 658L) */ ((
					var_1_26
				) + (
					-2
				))
			);
		} else {
			/* 917L, 207L, 629L, 661L) */ var_1_24 = (
				var_1_16
			);
		}
	} else {
		/* 921L, 213L, 633L, 665L) */ var_1_24 = (
			var_1_26
		);
	}


	// From: Req7Batch167Filler_PE_CI
	/* 926L, 244L, 734L, 750L) */ if (/* 927L, 225L, 226L, 735L, 751L) */ ((var_1_1) >= (/* 929L, 224L, 228L, 737L, 753L) */ (abs (var_1_10))))) {
		/* 931L, 239L, 739L, 755L) */ var_1_27 = (
			/* 934L, 238L, 742L, 758L) */ ((
				var_1_28
			) || (
				var_1_29
			))
		);
	} else {
		/* 937L, 243L, 745L, 761L) */ var_1_27 = (
			var_1_30
		);
	}


	// From: Req4Batch167Filler_PE_CI
	unsigned long int stepLocal_2 = var_1_5;
	/* 878L, 134L, 482L, 501L) */ if (/* 867L, 109L, 110L, 483L, 502L) */ ((/* 866L, 107L, 111L, 484L, 503L) */ ((/* 864L, 105L, 112L, 485L, 504L) */ (max (/* 864L, 105L, 112L, 485L, 504L) */ (var_1_3) , (var_1_18)))) * (var_1_4))) == (stepLocal_2))) {
		/* 873L, 129L, 490L, 509L) */ var_1_17 = (
			/* 872L, 128L, 493L, 512L) */ ((
				-1
			) - (
				var_1_19
			))
		);
	} else {
		/* 877L, 133L, 496L, 515L) */ var_1_17 = (
			var_1_24
		);
	}


	// From: CodeObject1
	/* 242L, 10L) */ if (var_1_15) {
		/* 244L, 9L) */ var_1_31 = (
			/* 247L, 8L) */ (abs (
				var_1_33
			))
		);
	}


	// From: CodeObject2
	/* 250L, 43L) */ if (/* 251L, 18L, 19L) */ ((/* 252L, 16L, 20L) */ ((var_1_33) > (var_1_11))) && (var_1_14))) {
		/* 256L, 36L) */ var_1_34 = (
			/* 259L, 35L) */ (min (
				/* 259L, 35L) */ (
					var_1_35
				) , (
					/* 261L, 34L) */ ((
						var_1_36
					) + (
						var_1_37
					))
				)
			))
		);
	} else {
		/* 264L, 42L) */ var_1_34 = (
			/* 267L, 41L) */ ((
				var_1_37
			) + (
				var_1_36
			))
		);
	}


	// From: CodeObject3
	/* 271L, 52L) */ var_1_38 = (
		var_1_21
	);


	// From: CodeObject4
	/* 276L, 60L) */ var_1_40 = (
		var_1_28
	);


	// From: CodeObject5
	/* 280L, 92L) */ if (/* 281L, 70L, 71L) */ ((/* 282L, 68L, 72L) */ ((/* 283L, 66L, 73L) */ (- (var_1_35))) / (var_1_43))) > (var_1_36))) {
		/* 287L, 91L) */ var_1_42 = (
			/* 290L, 90L) */ (max (
				/* 290L, 90L) */ (
					/* 291L, 88L) */ (abs (
						/* 292L, 87L) */ (min (
							/* 292L, 87L) */ (
								var_1_21
							) , (
								var_1_23
							)
						))
					))
				) , (
					var_1_43
				)
			))
		);
	}


	// From: CodeObject6
	/* 296L, 104L) */ if (var_1_30) {
		/* 298L, 103L) */ var_1_44 = (
			/* 301L, 102L) */ (abs (
				var_1_33
			))
		);
	}


	// From: CodeObject7
	/* 304L, 112L) */ var_1_45 = (
		/* 307L, 111L) */ (abs (
			var_1_33
		))
	);


	// From: CodeObject8
	/* 347L, 178L) */ if (/* 348L, 121L, 122L) */ ((var_1_21) < (/* 350L, 120L, 124L) */ ((var_1_4) / (10))))) {
		/* 353L, 154L) */ if (/* 354L, 134L, 135L) */ ((var_1_47) <= (var_1_48))) {
			/* 357L, 144L) */ var_1_46 = (
				var_1_49
			);
		} else {
			/* 361L, 153L) */ var_1_46 = (
				/* 364L, 152L) */ (max (
					/* 364L, 152L) */ (
						/* 365L, 150L) */ ((
							/* 366L, 148L) */ (abs (
								1
							))
						) + (
							var_1_50
						))
					) , (
						var_1_49
					)
				))
			);
		}
	} else {
		/* 370L, 176L) */ if (/* 371L, 158L, 159L) */ ((var_1_4) >= (var_1_5))) {
			/* 374L, 171L) */ var_1_46 = (
				/* 377L, 170L) */ (abs (
					/* 378L, 169L) */ (max (
						/* 378L, 169L) */ (
							var_1_49
						) , (
							var_1_50
						)
					))
				))
			);
		} else {
			/* 381L, 175L) */ var_1_46 = (
				var_1_49
			);
		}
	}


	// From: CodeObject9
	/* 386L, 238L) */ if (/* 387L, 192L, 193L) */ ((/* 388L, 186L, 194L) */ ((/* 389L, 184L, 195L) */ ((var_1_23) - (var_1_50))) & (var_1_3))) >= (/* 393L, 191L, 199L) */ ((/* 394L, 189L, 200L) */ (max (/* 394L, 189L, 200L) */ (var_1_52) , (var_1_53)))) - (var_1_43))))) {
		/* 398L, 232L) */ if (/* 399L, 217L, 218L) */ ((var_1_49) > (var_1_21))) {
			/* 402L, 227L) */ var_1_51 = (
				var_1_49
			);
		} else {
			/* 406L, 231L) */ var_1_51 = (
				var_1_43
			);
		}
	} else {
		/* 410L, 237L) */ var_1_51 = (
			-2
		);
	}
}



void updateVariables(void) {
	var_1_2 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_2 >= 0);
	assume_abort_if_not(var_1_2 <= 1);
	var_1_3 = __VERIFIER_nondet_ulong();
	assume_abort_if_not(var_1_3 >= 0);
	assume_abort_if_not(var_1_3 <= 4294967295);
	var_1_4 = __VERIFIER_nondet_ulong();
	assume_abort_if_not(var_1_4 >= 0);
	assume_abort_if_not(var_1_4 <= 4294967295);
	var_1_5 = __VERIFIER_nondet_ulong();
	assume_abort_if_not(var_1_5 >= 0);
	assume_abort_if_not(var_1_5 <= 4294967295);
	var_1_6 = __VERIFIER_nondet_float();
	assume_abort_if_not((var_1_6 >= 0.0F && var_1_6 <= -1.0e-20F) || (var_1_6 <= 2305843.009213691400e+12F && var_1_6 >= 1.0e-20F ));
	var_1_7 = __VERIFIER_nondet_float();
	assume_abort_if_not((var_1_7 >= 0.0F && var_1_7 <= -1.0e-20F) || (var_1_7 <= 2305843.009213691400e+12F && var_1_7 >= 1.0e-20F ));
	var_1_8 = __VERIFIER_nondet_float();
	assume_abort_if_not((var_1_8 >= 0.0F && var_1_8 <= -1.0e-20F) || (var_1_8 <= 4611686.018427383000e+12F && var_1_8 >= 1.0e-20F ));
	var_1_9 = __VERIFIER_nondet_float();
	assume_abort_if_not((var_1_9 >= 0.0F && var_1_9 <= -1.0e-20F) || (var_1_9 <= 4611686.018427383000e+12F && var_1_9 >= 1.0e-20F ));
	var_1_10 = __VERIFIER_nondet_float();
	assume_abort_if_not((var_1_10 >= 0.0F && var_1_10 <= -1.0e-20F) || (var_1_10 <= 9223372.036854766000e+12F && var_1_10 >= 1.0e-20F ));
	var_1_12 = __VERIFIER_nondet_float();
	assume_abort_if_not((var_1_12 >= -922337.2036854776000e+13F && var_1_12 <= -1.0e-20F) || (var_1_12 <= 9223372.036854776000e+12F && var_1_12 >= 1.0e-20F ));
	assume_abort_if_not(var_1_12 != 0.0F);
	var_1_14 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_14 >= 0);
	assume_abort_if_not(var_1_14 <= 1);
	var_1_15 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_15 >= 0);
	assume_abort_if_not(var_1_15 <= 1);
	var_1_16 = __VERIFIER_nondet_char();
	assume_abort_if_not(var_1_16 >= -127);
	assume_abort_if_not(var_1_16 <= 126);
	var_1_18 = __VERIFIER_nondet_long();
	assume_abort_if_not(var_1_18 >= 0);
	assume_abort_if_not(var_1_18 <= 2147483647);
	var_1_19 = __VERIFIER_nondet_short();
	assume_abort_if_not(var_1_19 >= 0);
	assume_abort_if_not(var_1_19 <= 32766);
	var_1_21 = __VERIFIER_nondet_ushort();
	assume_abort_if_not(var_1_21 >= 0);
	assume_abort_if_not(var_1_21 <= 16384);
	var_1_22 = __VERIFIER_nondet_ushort();
	assume_abort_if_not(var_1_22 >= 0);
	assume_abort_if_not(var_1_22 <= 16384);
	var_1_23 = __VERIFIER_nondet_ushort();
	assume_abort_if_not(var_1_23 >= 0);
	assume_abort_if_not(var_1_23 <= 16383);
	var_1_25 = __VERIFIER_nondet_float();
	assume_abort_if_not((var_1_25 >= -922337.2036854776000e+13F && var_1_25 <= -1.0e-20F) || (var_1_25 <= 9223372.036854776000e+12F && var_1_25 >= 1.0e-20F ));
	assume_abort_if_not(var_1_25 != 0.0F);
	var_1_26 = __VERIFIER_nondet_char();
	assume_abort_if_not(var_1_26 >= -63);
	assume_abort_if_not(var_1_26 <= 63);
	var_1_28 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_28 >= 0);
	assume_abort_if_not(var_1_28 <= 0);
	var_1_29 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_29 >= 0);
	assume_abort_if_not(var_1_29 <= 0);
	var_1_30 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_30 >= 0);
	assume_abort_if_not(var_1_30 <= 0);
	var_1_33 = __VERIFIER_nondet_double();
	assume_abort_if_not((var_1_33 >= -922337.2036854766000e+13F && var_1_33 <= -1.0e-20F) || (var_1_33 <= 9223372.036854766000e+12F && var_1_33 >= 1.0e-20F ));
	var_1_35 = __VERIFIER_nondet_long();
	assume_abort_if_not(var_1_35 >= -2147483647);
	assume_abort_if_not(var_1_35 <= 2147483646);
	var_1_36 = __VERIFIER_nondet_long();
	assume_abort_if_not(var_1_36 >= -1073741823);
	assume_abort_if_not(var_1_36 <= 1073741823);
	var_1_37 = __VERIFIER_nondet_long();
	assume_abort_if_not(var_1_37 >= -1073741823);
	assume_abort_if_not(var_1_37 <= 1073741823);
	var_1_43 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_43 >= 0);
	assume_abort_if_not(var_1_43 <= 255);
	assume_abort_if_not(var_1_43 != 0);
	var_1_47 = __VERIFIER_nondet_double();
	assume_abort_if_not((var_1_47 >= -922337.2036854776000e+13F && var_1_47 <= -1.0e-20F) || (var_1_47 <= 9223372.036854776000e+12F && var_1_47 >= 1.0e-20F ));
	var_1_48 = __VERIFIER_nondet_double();
	assume_abort_if_not((var_1_48 >= -922337.2036854776000e+13F && var_1_48 <= -1.0e-20F) || (var_1_48 <= 9223372.036854776000e+12F && var_1_48 >= 1.0e-20F ));
	var_1_49 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_49 >= 0);
	assume_abort_if_not(var_1_49 <= 254);
	var_1_50 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_50 >= 0);
	assume_abort_if_not(var_1_50 <= 127);
	var_1_52 = __VERIFIER_nondet_ulong();
	assume_abort_if_not(var_1_52 >= 2147483647);
	assume_abort_if_not(var_1_52 <= 4294967295);
	var_1_53 = __VERIFIER_nondet_ulong();
	assume_abort_if_not(var_1_53 >= 2147483647);
	assume_abort_if_not(var_1_53 <= 4294967295);
}



void updateLastVariables(void) {
}

int property(void) {
	if (/* 415L, 7L, 13L, 295L, 318L, 943L) */ ((var_1_3) == (/* 417L, 6L, 15L, 297L, 320L, 945L) */ (max (/* 417L, 6L, 15L, 297L, 320L, 945L) */ (var_1_4) , (var_1_5)))))) {
	} else {
	}
	if (/* 438L, 46L, 54L, 379L, 398L, 966L) */ ((var_1_10) > (/* 440L, 45L, 56L, 381L, 400L, 968L) */ ((var_1_7) * (/* 442L, 44L, 58L, 383L, 402L, 970L) */ ((var_1_6) / (var_1_12))))))) {
	} else {
	}
	if (/* 457L, 81L, 87L, 461L, 472L, 985L) */ ((/* 458L, 79L, 88L, 462L, 473L, 986L) */ ((var_1_2) && (var_1_14))) && (var_1_15))) {
	}
	if (/* 468L, 109L, 117L, 521L, 540L, 996L) */ ((/* 469L, 107L, 118L, 522L, 541L, 997L) */ ((/* 470L, 105L, 119L, 523L, 542L, 998L) */ (max (/* 470L, 105L, 119L, 523L, 542L, 998L) */ (var_1_3) , (var_1_18)))) * (var_1_4))) == (var_1_5))) {
	} else {
	}
	if (/* 500L, 161L, 168L, 672L, 704L, 1028L) */ ((/* 501L, 159L, 169L, 673L, 705L, 1029L) */ (min (/* 501L, 159L, 169L, 673L, 705L, 1029L) */ (var_1_1) , (/* 503L, 158L, 171L, 675L, 707L, 1031L) */ (- (var_1_9)))))) > (var_1_8))) {
		if (/* 507L, 181L, 190L, 679L, 711L, 1035L) */ ((/* 508L, 179L, 191L, 680L, 712L, 1036L) */ ((/* 509L, 175L, 192L, 681L, 713L, 1037L) */ (abs (var_1_7))) / (/* 511L, 178L, 194L, 683L, 715L, 1039L) */ (max (/* 511L, 178L, 194L, 683L, 715L, 1039L) */ (var_1_12) , (var_1_25)))))) < (var_1_11))) {
		} else {
		}
	} else {
	}
	if (/* 531L, 225L, 230L, 767L, 783L, 1059L) */ ((var_1_1) >= (/* 533L, 224L, 232L, 769L, 785L, 1061L) */ (abs (var_1_10))))) {
	} else {
	}
	return /* 551L) */ ((
	/* 550L) */ ((
		/* 549L) */ ((
			/* 548L) */ ((
				/* 547L) */ ((
					/* 546L) */ ((
						/* 414L, 35L, 294L, 317L, 942L) */ ((
							/* 415L, 7L, 13L, 295L, 318L, 943L) */ ((
								var_1_3
							) == (
								/* 417L, 6L, 15L, 297L, 320L, 945L) */ (max (
									/* 417L, 6L, 15L, 297L, 320L, 945L) */ (
										var_1_4
									) , (
										var_1_5
									)
								))
							))
						) ? (
							/* 420L, 29L, 300L, 323L, 948L) */ ((
								var_1_1
							) == (
								/* 420L, 29L, 300L, 323L, 948L) */ ((float) (
									/* 423L, 28L, 303L, 326L, 951L) */ ((
										/* 424L, 26L, 304L, 327L, 952L) */ ((
											/* 425L, 22L, 305L, 328L, 953L) */ ((
												var_1_6
											) + (
												var_1_7
											))
										) + (
											/* 428L, 25L, 308L, 331L, 956L) */ (min (
												/* 428L, 25L, 308L, 331L, 956L) */ (
													var_1_8
												) , (
													var_1_9
												)
											))
										))
									) - (
										var_1_10
									))
								))
							))
						) : (
							/* 432L, 33L, 312L, 335L, 960L) */ ((
								var_1_1
							) == (
								/* 432L, 33L, 312L, 335L, 960L) */ ((float) (
									8.2f
								))
							))
						))
					) && (
						/* 437L, 72L, 378L, 397L, 965L) */ ((
							/* 438L, 46L, 54L, 379L, 398L, 966L) */ ((
								var_1_10
							) > (
								/* 440L, 45L, 56L, 381L, 400L, 968L) */ ((
									var_1_7
								) * (
									/* 442L, 44L, 58L, 383L, 402L, 970L) */ ((
										var_1_6
									) / (
										var_1_12
									))
								))
							))
						) ? (
							/* 445L, 66L, 386L, 405L, 973L) */ ((
								var_1_11
							) == (
								/* 445L, 66L, 386L, 405L, 973L) */ ((double) (
									/* 448L, 65L, 389L, 408L, 976L) */ ((
										var_1_7
									) - (
										var_1_9
									))
								))
							))
						) : (
							/* 451L, 70L, 392L, 411L, 979L) */ ((
								var_1_11
							) == (
								/* 451L, 70L, 392L, 411L, 979L) */ ((double) (
									var_1_8
								))
							))
						))
					))
				) && (
					/* 456L, 97L, 460L, 471L, 984L) */ ((
						/* 457L, 81L, 87L, 461L, 472L, 985L) */ ((
							/* 458L, 79L, 88L, 462L, 473L, 986L) */ ((
								var_1_2
							) && (
								var_1_14
							))
						) && (
							var_1_15
						))
					) ? (
						/* 462L, 95L, 466L, 477L, 990L) */ ((
							var_1_13
						) == (
							/* 462L, 95L, 466L, 477L, 990L) */ ((signed char) (
								var_1_16
							))
						))
					) : (
						1
					))
				))
			) && (
				/* 467L, 135L, 520L, 539L, 995L) */ ((
					/* 468L, 109L, 117L, 521L, 540L, 996L) */ ((
						/* 469L, 107L, 118L, 522L, 541L, 997L) */ ((
							/* 470L, 105L, 119L, 523L, 542L, 998L) */ (max (
								/* 470L, 105L, 119L, 523L, 542L, 998L) */ (
									var_1_3
								) , (
									var_1_18
								)
							))
						) * (
							var_1_4
						))
					) == (
						var_1_5
					))
				) ? (
					/* 475L, 129L, 528L, 547L, 1003L) */ ((
						var_1_17
					) == (
						/* 475L, 129L, 528L, 547L, 1003L) */ ((signed short int) (
							/* 478L, 128L, 531L, 550L, 1006L) */ ((
								-1
							) - (
								var_1_19
							))
						))
					))
				) : (
					/* 481L, 133L, 534L, 553L, 1009L) */ ((
						var_1_17
					) == (
						/* 481L, 133L, 534L, 553L, 1009L) */ ((signed short int) (
							var_1_24
						))
					))
				))
			))
		) && (
			/* 487L, 149L, 583L, 595L, 1015L) */ ((
				var_1_20
			) == (
				/* 487L, 149L, 583L, 595L, 1015L) */ ((unsigned short int) (
					/* 490L, 148L, 586L, 598L, 1018L) */ ((
						/* 491L, 144L, 587L, 599L, 1019L) */ ((
							var_1_21
						) + (
							16
						))
					) + (
						/* 494L, 147L, 590L, 602L, 1022L) */ ((
							var_1_22
						) + (
							var_1_23
						))
					))
				))
			))
		))
	) && (
		/* 499L, 215L, 671L, 703L, 1027L) */ ((
			/* 500L, 161L, 168L, 672L, 704L, 1028L) */ ((
				/* 501L, 159L, 169L, 673L, 705L, 1029L) */ (min (
					/* 501L, 159L, 169L, 673L, 705L, 1029L) */ (
						var_1_1
					) , (
						/* 503L, 158L, 171L, 675L, 707L, 1031L) */ (- (
							var_1_9
						))
					)
				))
			) > (
				var_1_8
			))
		) ? (
			/* 506L, 209L, 678L, 710L, 1034L) */ ((
				/* 507L, 181L, 190L, 679L, 711L, 1035L) */ ((
					/* 508L, 179L, 191L, 680L, 712L, 1036L) */ ((
						/* 509L, 175L, 192L, 681L, 713L, 1037L) */ (abs (
							var_1_7
						))
					) / (
						/* 511L, 178L, 194L, 683L, 715L, 1039L) */ (max (
							/* 511L, 178L, 194L, 683L, 715L, 1039L) */ (
								var_1_12
							) , (
								var_1_25
							)
						))
					))
				) < (
					var_1_11
				))
			) ? (
				/* 515L, 203L, 687L, 719L, 1043L) */ ((
					var_1_24
				) == (
					/* 515L, 203L, 687L, 719L, 1043L) */ ((signed char) (
						/* 518L, 202L, 690L, 722L, 1046L) */ ((
							var_1_26
						) + (
							-2
						))
					))
				))
			) : (
				/* 521L, 207L, 693L, 725L, 1049L) */ ((
					var_1_24
				) == (
					/* 521L, 207L, 693L, 725L, 1049L) */ ((signed char) (
						var_1_16
					))
				))
			))
		) : (
			/* 525L, 213L, 697L, 729L, 1053L) */ ((
				var_1_24
			) == (
				/* 525L, 213L, 697L, 729L, 1053L) */ ((signed char) (
					var_1_26
				))
			))
		))
	))
) && (
	/* 530L, 245L, 766L, 782L, 1058L) */ ((
		/* 531L, 225L, 230L, 767L, 783L, 1059L) */ ((
			var_1_1
		) >= (
			/* 533L, 224L, 232L, 769L, 785L, 1061L) */ (abs (
				var_1_10
			))
		))
	) ? (
		/* 535L, 239L, 771L, 787L, 1063L) */ ((
			var_1_27
		) == (
			/* 535L, 239L, 771L, 787L, 1063L) */ ((unsigned char) (
				/* 538L, 238L, 774L, 790L, 1066L) */ ((
					var_1_28
				) || (
					var_1_29
				))
			))
		))
	) : (
		/* 541L, 243L, 777L, 793L, 1069L) */ ((
			var_1_27
		) == (
			/* 541L, 243L, 777L, 793L, 1069L) */ ((unsigned char) (
				var_1_30
			))
		))
	))
))
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
