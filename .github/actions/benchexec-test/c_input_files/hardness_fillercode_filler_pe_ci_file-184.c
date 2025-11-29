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
void reach_error(void) { __assert_fail("0", "Req1_Prop1_Batch184Filler_PE_CI.c", 13, "reach_error"); }
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
unsigned char var_1_2 = 100;
unsigned char var_1_3 = 100;
unsigned char var_1_4 = 100;
signed long int var_1_5 = -4;
unsigned char var_1_6 = 0;
unsigned char var_1_7 = 0;
unsigned char var_1_8 = 4;
unsigned char var_1_9 = 128;
unsigned char var_1_10 = 200;
unsigned char var_1_11 = 2;
double var_1_12 = 128.75;
double var_1_13 = 499.9;
double var_1_14 = 127.6;
double var_1_15 = 7.5;
double var_1_16 = 15.25;
unsigned char var_1_17 = 1;
double var_1_18 = 0.09999999999999998;
double var_1_19 = 1.375;
float var_1_20 = 100000000000000.5;
unsigned short int var_1_22 = 200;
signed long int var_1_23 = -10;
signed long int var_1_24 = -10;
unsigned long int var_1_25 = 64;
signed long int var_1_26 = -32;
unsigned long int var_1_29 = 256;
float var_1_30 = 8.4;
double var_1_32 = 256.75;
signed char var_1_34 = -5;
signed char var_1_35 = 50;
signed char var_1_36 = 32;
signed char var_1_37 = 16;
signed char var_1_38 = 8;
signed char var_1_39 = 2;
signed char var_1_40 = -16;
unsigned char var_1_41 = 0;
unsigned char var_1_42 = 1;
unsigned char var_1_43 = 5;
unsigned char var_1_45 = 0;
unsigned char var_1_46 = 25;
unsigned long int var_1_47 = 0;
unsigned char var_1_48 = 10;
unsigned short int var_1_49 = 32;

// Calibration values

// Last'ed variables

// Additional functions


void initially(void) {
}



void step(void) {
	// From: Req2Batch184Filler_PE_CI
	signed long int stepLocal_0 = var_1_5;
	/* 924L, 98L, 389L, 412L) */ if (/* 905L, 73L, 74L, 390L, 413L) */ ((var_1_4) <= (stepLocal_0))) {
		/* 915L, 89L, 393L, 416L) */ var_1_8 = (
			/* 914L, 88L, 396L, 419L) */ ((
				/* 910L, 84L, 397L, 420L) */ (min (
					/* 910L, 84L, 397L, 420L) */ (
						var_1_9
					) , (
						var_1_10
					)
				))
			) - (
				/* 913L, 87L, 400L, 423L) */ ((
					64
				) - (
					var_1_11
				))
			))
		);
	} else {
		/* 923L, 97L, 403L, 426L) */ var_1_8 = (
			/* 922L, 96L, 406L, 429L) */ (max (
				/* 922L, 96L, 406L, 429L) */ (
					/* 920L, 94L, 407L, 430L) */ (min (
						/* 920L, 94L, 407L, 430L) */ (
							var_1_9
						) , (
							var_1_11
						)
					))
				) , (
					var_1_10
				)
			))
		);
	}


	// From: Req3Batch184Filler_PE_CI
	signed long int stepLocal_1 = var_1_5;
	/* 949L, 137L, 481L, 502L) */ if (/* 936L, 110L, 111L, 482L, 503L) */ ((/* 935L, 108L, 112L, 483L, 504L) */ ((/* 933L, 106L, 113L, 484L, 505L) */ ((var_1_10) | (var_1_4))) * (var_1_8))) <= (stepLocal_1))) {
		/* 942L, 130L, 489L, 510L) */ var_1_12 = (
			/* 941L, 129L, 492L, 513L) */ ((
				var_1_13
			) - (
				var_1_14
			))
		);
	} else {
		/* 948L, 136L, 495L, 516L) */ var_1_12 = (
			/* 947L, 135L, 498L, 519L) */ ((
				var_1_15
			) + (
				var_1_16
			))
		);
	}


	// From: Req4Batch184Filler_PE_CI
	/* 955L, 168L, 567L, 582L) */ if (/* 956L, 149L, 150L, 568L, 583L) */ ((var_1_14) <= (/* 958L, 148L, 152L, 570L, 585L) */ (max (/* 958L, 148L, 152L, 570L, 585L) */ (var_1_13) , (/* 960L, 147L, 154L, 572L, 587L) */ ((var_1_18) - (var_1_19)))))))) {
		/* 963L, 167L, 575L, 590L) */ var_1_17 = (
			var_1_6
		);
	}


	// From: Req1Batch184Filler_PE_CI
	/* 870L, 63L, 262L, 294L) */ if (/* 871L, 8L, 9L, 263L, 295L) */ ((/* 872L, 6L, 10L, 264L, 296L) */ ((var_1_8) / (/* 874L, 5L, 12L, 266L, 298L) */ (min (/* 874L, 5L, 12L, 266L, 298L) */ (var_1_3) , (var_1_4)))))) <= (var_1_5))) {
		/* 878L, 57L, 270L, 302L) */ if (/* 879L, 25L, 26L, 271L, 303L) */ ((var_1_4) >= (100))) {
			/* 882L, 35L, 274L, 306L) */ var_1_1 = (
				var_1_6
			);
		} else {
			/* 886L, 55L, 278L, 310L) */ if (var_1_6) {
				/* 888L, 42L, 280L, 312L) */ var_1_1 = (
					var_1_7
				);
			} else {
				/* 892L, 54L, 284L, 316L) */ var_1_1 = (
					0
				);
			}
		}
	} else {
		/* 896L, 62L, 288L, 320L) */ var_1_1 = (
			0
		);
	}


	// From: Req5Batch184Filler_PE_CI
	unsigned char stepLocal_2 = var_1_7;
	/* 990L, 211L, 625L, 647L) */ if (/* 974L, 182L, 183L, 626L, 648L) */ ((stepLocal_2) || (/* 973L, 181L, 185L, 628L, 650L) */ ((var_1_17) || (var_1_6))))) {
		/* 983L, 203L, 631L, 653L) */ if (var_1_1) {
			/* 982L, 202L, 633L, 655L) */ var_1_20 = (
				/* 981L, 201L, 636L, 658L) */ (min (
					/* 981L, 201L, 636L, 658L) */ (
						var_1_15
					) , (
						/* 980L, 200L, 638L, 660L) */ (abs (
							var_1_16
						))
					)
				))
			);
		}
	} else {
		/* 989L, 210L, 640L, 662L) */ var_1_20 = (
			/* 988L, 209L, 643L, 665L) */ ((
				var_1_16
			) + (
				var_1_15
			))
		);
	}


	// From: Req6Batch184Filler_PE_CI
	/* 995L, 255L, 766L, 792L) */ if (/* 996L, 218L, 219L, 767L, 793L) */ (! (var_1_1))) {
		/* 998L, 229L, 769L, 795L) */ var_1_22 = (
			/* 1001L, 228L, 772L, 798L) */ (abs (
				/* 1002L, 227L, 773L, 799L) */ (min (
					/* 1002L, 227L, 773L, 799L) */ (
						var_1_8
					) , (
						var_1_2
					)
				))
			))
		);
	} else {
		/* 1005L, 253L, 776L, 802L) */ if (/* 1006L, 234L, 235L, 777L, 803L) */ ((1) < (/* 1008L, 233L, 237L, 779L, 805L) */ ((var_1_3) + (var_1_5))))) {
			/* 1011L, 248L, 782L, 808L) */ var_1_22 = (
				var_1_9
			);
		} else {
			/* 1015L, 252L, 786L, 812L) */ var_1_22 = (
				var_1_8
			);
		}
	}


	// From: CodeObject1
	/* 257L, 5L) */ var_1_23 = (
		var_1_24
	);


	// From: CodeObject2
	/* 274L, 37L) */ if (/* 275L, 13L, 14L) */ ((var_1_24) > (/* 277L, 12L, 16L) */ (abs (var_1_26))))) {
		/* 279L, 35L) */ if (/* 280L, 24L, 25L) */ ((var_1_1) && (var_1_7))) {
			/* 283L, 34L) */ var_1_25 = (
				var_1_29
			);
		}
	}


	// From: CodeObject3
	/* 289L, 44L) */ var_1_30 = (
		var_1_14
	);


	// From: CodeObject4
	/* 294L, 82L) */ if (/* 295L, 62L, 63L) */ ((/* 296L, 59L, 64L) */ (- (/* 297L, 58L, 65L) */ ((var_1_26) ^ (var_1_25))))) < (/* 300L, 61L, 68L) */ (abs (var_1_29))))) {
		/* 302L, 81L) */ var_1_32 = (
			/* 305L, 80L) */ (abs (
				var_1_14
			))
		);
	}


	// From: CodeObject5
	/* 338L, 138L) */ if (/* 339L, 90L, 91L) */ ((var_1_29) <= (var_1_5))) {
		/* 342L, 125L) */ if (/* 343L, 104L, 105L) */ ((/* 344L, 102L, 106L) */ ((var_1_24) & (var_1_29))) > (var_1_5))) {
			/* 348L, 124L) */ var_1_34 = (
				/* 351L, 123L) */ ((
					/* 352L, 121L) */ (max (
						/* 352L, 121L) */ (
							/* 353L, 119L) */ (max (
								/* 353L, 119L) */ (
									var_1_35
								) , (
									var_1_36
								)
							))
						) , (
							var_1_37
						)
					))
				) + (
					var_1_38
				))
			);
		}
	} else {
		/* 358L, 137L) */ var_1_34 = (
			/* 361L, 136L) */ (max (
				/* 361L, 136L) */ (
					/* 362L, 132L) */ ((
						var_1_39
					) - (
						/* 364L, 131L) */ (abs (
							var_1_38
						))
					))
				) , (
					/* 366L, 135L) */ ((
						var_1_36
					) + (
						var_1_40
					))
				)
			))
		);
	}


	// From: CodeObject6
	/* 382L, 160L) */ if (/* 383L, 145L, 146L) */ ((var_1_11) > (/* 385L, 144L, 148L) */ (abs (var_1_11))))) {
		/* 387L, 159L) */ var_1_41 = (
			/* 390L, 158L) */ ((
				var_1_7
			) || (
				var_1_42
			))
		);
	}


	// From: CodeObject7
	/* 411L, 195L) */ if (/* 412L, 172L, 173L) */ ((var_1_5) <= (/* 414L, 171L, 175L) */ ((var_1_36) ^ (/* 416L, 170L, 177L) */ ((-4) ^ (var_1_25))))))) {
		/* 419L, 194L) */ var_1_43 = (
			/* 422L, 193L) */ (min (
				/* 422L, 193L) */ (
					var_1_10
				) , (
					/* 424L, 192L) */ ((
						var_1_45
					) + (
						var_1_46
					))
				)
			))
		);
	}


	// From: CodeObject8
	/* 428L, 236L) */ if (var_1_17) {
		/* 430L, 209L) */ var_1_47 = (
			/* 433L, 208L) */ (max (
				/* 433L, 208L) */ (
					1u
				) , (
					var_1_10
				)
			))
		);
	} else {
		/* 436L, 234L) */ if (/* 437L, 219L, 220L) */ ((var_1_11) > (/* 439L, 218L, 222L) */ (max (/* 439L, 218L, 222L) */ (-2) , (var_1_11)))))) {
			/* 442L, 233L) */ var_1_47 = (
				var_1_11
			);
		}
	}


	// From: CodeObject9
	/* 447L, 245L) */ var_1_48 = (
		var_1_11
	);


	// From: CodeObject10
	/* 452L, 253L) */ var_1_49 = (
		var_1_10
	);
}



void updateVariables(void) {
	var_1_2 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_2 >= 0);
	assume_abort_if_not(var_1_2 <= 255);
	var_1_3 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_3 >= 0);
	assume_abort_if_not(var_1_3 <= 255);
	assume_abort_if_not(var_1_3 != 0);
	var_1_4 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_4 >= 0);
	assume_abort_if_not(var_1_4 <= 255);
	assume_abort_if_not(var_1_4 != 0);
	var_1_5 = __VERIFIER_nondet_long();
	assume_abort_if_not(var_1_5 >= -2147483648);
	assume_abort_if_not(var_1_5 <= 2147483647);
	var_1_6 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_6 >= 1);
	assume_abort_if_not(var_1_6 <= 1);
	var_1_7 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_7 >= 0);
	assume_abort_if_not(var_1_7 <= 0);
	var_1_9 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_9 >= 127);
	assume_abort_if_not(var_1_9 <= 254);
	var_1_10 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_10 >= 127);
	assume_abort_if_not(var_1_10 <= 254);
	var_1_11 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_11 >= 0);
	assume_abort_if_not(var_1_11 <= 63);
	var_1_13 = __VERIFIER_nondet_double();
	assume_abort_if_not((var_1_13 >= 0.0F && var_1_13 <= -1.0e-20F) || (var_1_13 <= 9223372.036854766000e+12F && var_1_13 >= 1.0e-20F ));
	var_1_14 = __VERIFIER_nondet_double();
	assume_abort_if_not((var_1_14 >= 0.0F && var_1_14 <= -1.0e-20F) || (var_1_14 <= 9223372.036854766000e+12F && var_1_14 >= 1.0e-20F ));
	var_1_15 = __VERIFIER_nondet_double();
	assume_abort_if_not((var_1_15 >= -461168.6018427383000e+13F && var_1_15 <= -1.0e-20F) || (var_1_15 <= 4611686.018427383000e+12F && var_1_15 >= 1.0e-20F ));
	var_1_16 = __VERIFIER_nondet_double();
	assume_abort_if_not((var_1_16 >= -461168.6018427383000e+13F && var_1_16 <= -1.0e-20F) || (var_1_16 <= 4611686.018427383000e+12F && var_1_16 >= 1.0e-20F ));
	var_1_18 = __VERIFIER_nondet_double();
	assume_abort_if_not((var_1_18 >= 0.0F && var_1_18 <= -1.0e-20F) || (var_1_18 <= 9223372.036854776000e+12F && var_1_18 >= 1.0e-20F ));
	var_1_19 = __VERIFIER_nondet_double();
	assume_abort_if_not((var_1_19 >= 0.0F && var_1_19 <= -1.0e-20F) || (var_1_19 <= 9223372.036854776000e+12F && var_1_19 >= 1.0e-20F ));
	var_1_24 = __VERIFIER_nondet_long();
	assume_abort_if_not(var_1_24 >= -2147483647);
	assume_abort_if_not(var_1_24 <= 2147483646);
	var_1_26 = __VERIFIER_nondet_long();
	assume_abort_if_not(var_1_26 >= -2147483647);
	assume_abort_if_not(var_1_26 <= 2147483647);
	var_1_29 = __VERIFIER_nondet_ulong();
	assume_abort_if_not(var_1_29 >= 0);
	assume_abort_if_not(var_1_29 <= 4294967294);
	var_1_35 = __VERIFIER_nondet_char();
	assume_abort_if_not(var_1_35 >= -63);
	assume_abort_if_not(var_1_35 <= 63);
	var_1_36 = __VERIFIER_nondet_char();
	assume_abort_if_not(var_1_36 >= -63);
	assume_abort_if_not(var_1_36 <= 63);
	var_1_37 = __VERIFIER_nondet_char();
	assume_abort_if_not(var_1_37 >= -63);
	assume_abort_if_not(var_1_37 <= 63);
	var_1_38 = __VERIFIER_nondet_char();
	assume_abort_if_not(var_1_38 >= -63);
	assume_abort_if_not(var_1_38 <= 63);
	var_1_39 = __VERIFIER_nondet_char();
	assume_abort_if_not(var_1_39 >= -1);
	assume_abort_if_not(var_1_39 <= 126);
	var_1_40 = __VERIFIER_nondet_char();
	assume_abort_if_not(var_1_40 >= -63);
	assume_abort_if_not(var_1_40 <= 63);
	var_1_42 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_42 >= 1);
	assume_abort_if_not(var_1_42 <= 1);
	var_1_45 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_45 >= 0);
	assume_abort_if_not(var_1_45 <= 127);
	var_1_46 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_46 >= 0);
	assume_abort_if_not(var_1_46 <= 127);
}



void updateLastVariables(void) {
}

int property(void) {
	if (/* 458L, 8L, 16L, 327L, 359L, 1022L) */ ((/* 459L, 6L, 17L, 328L, 360L, 1023L) */ ((var_1_8) / (/* 461L, 5L, 19L, 330L, 362L, 1025L) */ (min (/* 461L, 5L, 19L, 330L, 362L, 1025L) */ (var_1_3) , (var_1_4)))))) <= (var_1_5))) {
		if (/* 466L, 25L, 29L, 335L, 367L, 1030L) */ ((var_1_4) >= (100))) {
		} else {
			if (var_1_6) {
			} else {
			}
		}
	} else {
	}
	if (/* 489L, 73L, 77L, 436L, 459L, 1053L) */ ((var_1_4) <= (var_1_5))) {
	} else {
	}
	if (/* 512L, 110L, 118L, 524L, 545L, 1076L) */ ((/* 513L, 108L, 119L, 525L, 546L, 1077L) */ ((/* 514L, 106L, 120L, 526L, 547L, 1078L) */ ((var_1_10) | (var_1_4))) * (var_1_8))) <= (var_1_5))) {
	} else {
	}
	if (/* 535L, 149L, 157L, 598L, 613L, 1099L) */ ((var_1_14) <= (/* 537L, 148L, 159L, 600L, 615L, 1101L) */ (max (/* 537L, 148L, 159L, 600L, 615L, 1101L) */ (var_1_13) , (/* 539L, 147L, 161L, 602L, 617L, 1103L) */ ((var_1_18) - (var_1_19)))))))) {
	}
	if (/* 548L, 182L, 188L, 670L, 692L, 1112L) */ ((var_1_7) || (/* 550L, 181L, 190L, 672L, 694L, 1114L) */ ((var_1_17) || (var_1_6))))) {
		if (var_1_1) {
		}
	} else {
	}
	if (/* 571L, 218L, 221L, 819L, 845L, 1135L) */ (! (var_1_1))) {
	} else {
		if (/* 581L, 234L, 240L, 829L, 855L, 1145L) */ ((1) < (/* 583L, 233L, 242L, 831L, 857L, 1147L) */ ((var_1_3) + (var_1_5))))) {
		} else {
		}
	}
	return /* 599L) */ ((
	/* 598L) */ ((
		/* 597L) */ ((
			/* 596L) */ ((
				/* 595L) */ ((
					/* 457L, 64L, 326L, 358L, 1021L) */ ((
						/* 458L, 8L, 16L, 327L, 359L, 1022L) */ ((
							/* 459L, 6L, 17L, 328L, 360L, 1023L) */ ((
								var_1_8
							) / (
								/* 461L, 5L, 19L, 330L, 362L, 1025L) */ (min (
									/* 461L, 5L, 19L, 330L, 362L, 1025L) */ (
										var_1_3
									) , (
										var_1_4
									)
								))
							))
						) <= (
							var_1_5
						))
					) ? (
						/* 465L, 58L, 334L, 366L, 1029L) */ ((
							/* 466L, 25L, 29L, 335L, 367L, 1030L) */ ((
								var_1_4
							) >= (
								100
							))
						) ? (
							/* 469L, 35L, 338L, 370L, 1033L) */ ((
								var_1_1
							) == (
								/* 469L, 35L, 338L, 370L, 1033L) */ ((unsigned char) (
									var_1_6
								))
							))
						) : (
							/* 473L, 56L, 342L, 374L, 1037L) */ ((
								var_1_6
							) ? (
								/* 475L, 42L, 344L, 376L, 1039L) */ ((
									var_1_1
								) == (
									/* 475L, 42L, 344L, 376L, 1039L) */ ((unsigned char) (
										var_1_7
									))
								))
							) : (
								/* 479L, 54L, 348L, 380L, 1043L) */ ((
									var_1_1
								) == (
									/* 479L, 54L, 348L, 380L, 1043L) */ ((unsigned char) (
										0
									))
								))
							))
						))
					) : (
						/* 483L, 62L, 352L, 384L, 1047L) */ ((
							var_1_1
						) == (
							/* 483L, 62L, 352L, 384L, 1047L) */ ((unsigned char) (
								0
							))
						))
					))
				) && (
					/* 488L, 99L, 435L, 458L, 1052L) */ ((
						/* 489L, 73L, 77L, 436L, 459L, 1053L) */ ((
							var_1_4
						) <= (
							var_1_5
						))
					) ? (
						/* 492L, 89L, 439L, 462L, 1056L) */ ((
							var_1_8
						) == (
							/* 492L, 89L, 439L, 462L, 1056L) */ ((unsigned char) (
								/* 495L, 88L, 442L, 465L, 1059L) */ ((
									/* 496L, 84L, 443L, 466L, 1060L) */ (min (
										/* 496L, 84L, 443L, 466L, 1060L) */ (
											var_1_9
										) , (
											var_1_10
										)
									))
								) - (
									/* 499L, 87L, 446L, 469L, 1063L) */ ((
										64
									) - (
										var_1_11
									))
								))
							))
						))
					) : (
						/* 502L, 97L, 449L, 472L, 1066L) */ ((
							var_1_8
						) == (
							/* 502L, 97L, 449L, 472L, 1066L) */ ((unsigned char) (
								/* 505L, 96L, 452L, 475L, 1069L) */ (max (
									/* 505L, 96L, 452L, 475L, 1069L) */ (
										/* 506L, 94L, 453L, 476L, 1070L) */ (min (
											/* 506L, 94L, 453L, 476L, 1070L) */ (
												var_1_9
											) , (
												var_1_11
											)
										))
									) , (
										var_1_10
									)
								))
							))
						))
					))
				))
			) && (
				/* 511L, 138L, 523L, 544L, 1075L) */ ((
					/* 512L, 110L, 118L, 524L, 545L, 1076L) */ ((
						/* 513L, 108L, 119L, 525L, 546L, 1077L) */ ((
							/* 514L, 106L, 120L, 526L, 547L, 1078L) */ ((
								var_1_10
							) | (
								var_1_4
							))
						) * (
							var_1_8
						))
					) <= (
						var_1_5
					))
				) ? (
					/* 519L, 130L, 531L, 552L, 1083L) */ ((
						var_1_12
					) == (
						/* 519L, 130L, 531L, 552L, 1083L) */ ((double) (
							/* 522L, 129L, 534L, 555L, 1086L) */ ((
								var_1_13
							) - (
								var_1_14
							))
						))
					))
				) : (
					/* 525L, 136L, 537L, 558L, 1089L) */ ((
						var_1_12
					) == (
						/* 525L, 136L, 537L, 558L, 1089L) */ ((double) (
							/* 528L, 135L, 540L, 561L, 1092L) */ ((
								var_1_15
							) + (
								var_1_16
							))
						))
					))
				))
			))
		) && (
			/* 534L, 169L, 597L, 612L, 1098L) */ ((
				/* 535L, 149L, 157L, 598L, 613L, 1099L) */ ((
					var_1_14
				) <= (
					/* 537L, 148L, 159L, 600L, 615L, 1101L) */ (max (
						/* 537L, 148L, 159L, 600L, 615L, 1101L) */ (
							var_1_13
						) , (
							/* 539L, 147L, 161L, 602L, 617L, 1103L) */ ((
								var_1_18
							) - (
								var_1_19
							))
						)
					))
				))
			) ? (
				/* 542L, 167L, 605L, 620L, 1106L) */ ((
					var_1_17
				) == (
					/* 542L, 167L, 605L, 620L, 1106L) */ ((unsigned char) (
						var_1_6
					))
				))
			) : (
				1
			))
		))
	) && (
		/* 547L, 212L, 669L, 691L, 1111L) */ ((
			/* 548L, 182L, 188L, 670L, 692L, 1112L) */ ((
				var_1_7
			) || (
				/* 550L, 181L, 190L, 672L, 694L, 1114L) */ ((
					var_1_17
				) || (
					var_1_6
				))
			))
		) ? (
			/* 553L, 204L, 675L, 697L, 1117L) */ ((
				var_1_1
			) ? (
				/* 555L, 202L, 677L, 699L, 1119L) */ ((
					var_1_20
				) == (
					/* 555L, 202L, 677L, 699L, 1119L) */ ((float) (
						/* 558L, 201L, 680L, 702L, 1122L) */ (min (
							/* 558L, 201L, 680L, 702L, 1122L) */ (
								var_1_15
							) , (
								/* 560L, 200L, 682L, 704L, 1124L) */ (abs (
									var_1_16
								))
							)
						))
					))
				))
			) : (
				1
			))
		) : (
			/* 562L, 210L, 684L, 706L, 1126L) */ ((
				var_1_20
			) == (
				/* 562L, 210L, 684L, 706L, 1126L) */ ((float) (
					/* 565L, 209L, 687L, 709L, 1129L) */ ((
						var_1_16
					) + (
						var_1_15
					))
				))
			))
		))
	))
) && (
	/* 570L, 256L, 818L, 844L, 1134L) */ ((
		/* 571L, 218L, 221L, 819L, 845L, 1135L) */ (! (
			var_1_1
		))
	) ? (
		/* 573L, 229L, 821L, 847L, 1137L) */ ((
			var_1_22
		) == (
			/* 573L, 229L, 821L, 847L, 1137L) */ ((unsigned short int) (
				/* 576L, 228L, 824L, 850L, 1140L) */ (abs (
					/* 577L, 227L, 825L, 851L, 1141L) */ (min (
						/* 577L, 227L, 825L, 851L, 1141L) */ (
							var_1_8
						) , (
							var_1_2
						)
					))
				))
			))
		))
	) : (
		/* 580L, 254L, 828L, 854L, 1144L) */ ((
			/* 581L, 234L, 240L, 829L, 855L, 1145L) */ ((
				1
			) < (
				/* 583L, 233L, 242L, 831L, 857L, 1147L) */ ((
					var_1_3
				) + (
					var_1_5
				))
			))
		) ? (
			/* 586L, 248L, 834L, 860L, 1150L) */ ((
				var_1_22
			) == (
				/* 586L, 248L, 834L, 860L, 1150L) */ ((unsigned short int) (
					var_1_9
				))
			))
		) : (
			/* 590L, 252L, 838L, 864L, 1154L) */ ((
				var_1_22
			) == (
				/* 590L, 252L, 838L, 864L, 1154L) */ ((unsigned short int) (
					var_1_8
				))
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
