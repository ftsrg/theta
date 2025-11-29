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
void reach_error(void) { __assert_fail("0", "Req1_Prop1_Batch169Filler_PE_CI.c", 13, "reach_error"); }
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
signed long int var_1_1 = -16;
signed short int var_1_3 = 16;
signed short int var_1_4 = 25;
signed short int var_1_5 = -16;
signed short int var_1_6 = -10;
signed long int var_1_7 = 64;
signed long int var_1_8 = 2;
double var_1_9 = 24.25;
double var_1_10 = 255.5;
double var_1_11 = 1.875;
double var_1_12 = 100.6;
signed short int var_1_13 = 100;
signed short int var_1_14 = 8;
signed char var_1_15 = 25;
signed char var_1_16 = 4;
signed char var_1_17 = -10;
signed char var_1_18 = 1;
signed char var_1_19 = 25;
signed char var_1_20 = -5;
unsigned short int var_1_21 = 41146;
unsigned short int var_1_22 = 64;
unsigned short int var_1_23 = 5;
unsigned short int var_1_24 = 5;
unsigned short int var_1_25 = 5;
unsigned char var_1_26 = 128;
unsigned long int var_1_28 = 2263571286;
unsigned char var_1_29 = 16;
signed long int var_1_30 = -8;
float var_1_35 = 25.52;
unsigned char var_1_36 = 0;
float var_1_37 = 4.5;
signed long int var_1_38 = 25;
unsigned short int var_1_39 = 32;
signed char var_1_40 = -2;
unsigned char var_1_42 = 1;
unsigned char var_1_43 = 50;
unsigned char var_1_45 = 128;
unsigned char var_1_46 = 100;
unsigned short int var_1_47 = 100;
signed char var_1_48 = 25;

// Calibration values

// Last'ed variables
signed short int last_1_var_1_13 = 100;

// Additional functions


void initially(void) {
}



void step(void) {
	// From: Req1Batch169Filler_PE_CI
	/* 20L, 42L, 258L, 280L, 797L, 824L) */ if (/* 9L, 13L, 14L, 259L, 281L, 786L, 825L) */ ((last_1_var_1_13) < (/* 8L, 12L, 16L, 261L, 283L, 785L, 828L) */ ((/* 4L, 8L, 17L, 262L, 284L, 781L, 829L) */ ((var_1_3) - (var_1_4))) / (/* 7L, 11L, 20L, 265L, 287L, 784L, 832L) */ (max (/* 7L, 11L, 20L, 265L, 287L, 784L, 832L) */ (var_1_5) , (var_1_6)))))))) {
		/* 19L, 41L, 268L, 290L, 796L, 835L) */ var_1_1 = (
			/* 18L, 40L, 271L, 293L, 795L, 838L) */ ((
				var_1_3
			) - (
				/* 17L, 39L, 273L, 295L, 794L, 840L) */ (max (
					/* 17L, 39L, 273L, 295L, 794L, 840L) */ (
						/* 15L, 37L, 274L, 296L, 792L, 841L) */ (max (
							/* 15L, 37L, 274L, 296L, 792L, 841L) */ (
								64
							) , (
								var_1_4
							)
						))
					) , (
						var_1_7
					)
				))
			))
		);
	}


	// From: Req4Batch169Filler_PE_CI
	/* 873L, 114L, 450L, 463L) */ if (/* 874L, 97L, 98L, 451L, 464L) */ ((var_1_4) == (/* 876L, 96L, 100L, 453L, 466L) */ (~ (/* 877L, 95L, 101L, 454L, 467L) */ ((var_1_5) + (var_1_1))))))) {
		/* 880L, 113L, 457L, 470L) */ var_1_13 = (
			var_1_14
		);
	}


	// From: Req2Batch169Filler_PE_CI
	/* 847L, 64L, 346L, 357L) */ if (/* 848L, 52L, 53L, 347L, 358L) */ ((var_1_6) > (var_1_5))) {
		/* 851L, 63L, 350L, 361L) */ var_1_8 = (
			/* 854L, 62L, 353L, 364L) */ (abs (
				var_1_3
			))
		);
	}


	// From: Req3Batch169Filler_PE_CI
	/* 859L, 83L, 391L, 406L) */ var_1_9 = (
		/* 862L, 82L, 394L, 409L) */ ((
			/* 863L, 78L, 395L, 410L) */ (min (
				/* 863L, 78L, 395L, 410L) */ (
					var_1_10
				) , (
					/* 865L, 77L, 397L, 412L) */ ((
						1.000000000000005E14
					) + (
						256.1
					))
				)
			))
		) - (
			/* 868L, 81L, 400L, 415L) */ ((
				var_1_11
			) + (
				var_1_12
			))
		))
	);


	// From: Req5Batch169Filler_PE_CI
	/* 886L, 153L, 502L, 526L) */ if (/* 887L, 126L, 127L, 503L, 527L) */ ((var_1_14) > (/* 889L, 125L, 129L, 505L, 529L) */ (max (/* 889L, 125L, 129L, 505L, 529L) */ (var_1_1) , (-8)))))) {
		/* 892L, 146L, 508L, 532L) */ var_1_15 = (
			/* 895L, 145L, 511L, 535L) */ (min (
				/* 895L, 145L, 511L, 535L) */ (
					/* 896L, 143L, 512L, 536L) */ ((
						var_1_16
					) + (
						/* 898L, 142L, 514L, 538L) */ (max (
							/* 898L, 142L, 514L, 538L) */ (
								var_1_17
							) , (
								var_1_18
							)
						))
					))
				) , (
					var_1_19
				)
			))
		);
	} else {
		/* 902L, 152L, 518L, 542L) */ var_1_15 = (
			/* 905L, 151L, 521L, 545L) */ (min (
				/* 905L, 151L, 521L, 545L) */ (
					var_1_16
				) , (
					var_1_19
				)
			))
		);
	}


	// From: Req6Batch169Filler_PE_CI
	signed long int stepLocal_0 = /* 910L, 165L, 169L, 599L, 612L) */ ((/* 911L, 163L, 170L, 600L, 613L) */ ((var_1_21) - (var_1_4))) << (var_1_16));
	/* 922L, 186L, 597L, 610L) */ if (/* 917L, 167L, 168L, 598L, 611L) */ ((stepLocal_0) < (var_1_8))) {
		/* 921L, 185L, 605L, 618L) */ var_1_20 = (
			var_1_16
		);
	}


	// From: Req7Batch169Filler_PE_CI
	/* 927L, 201L, 650L, 662L) */ var_1_22 = (
		/* 930L, 200L, 653L, 665L) */ ((
			/* 931L, 196L, 654L, 666L) */ (min (
				/* 931L, 196L, 654L, 666L) */ (
					var_1_4
				) , (
					var_1_23
				)
			))
		) + (
			/* 934L, 199L, 657L, 669L) */ ((
				var_1_24
			) + (
				var_1_25
			))
		))
	);


	// From: Req8Batch169Filler_PE_CI
	signed long int stepLocal_2 = var_1_8;
	unsigned long int stepLocal_1 = /* 939L, 225L, 232L, 705L, 725L) */ ((5u) >> (16));
	/* 960L, 253L, 697L, 717L) */ if (/* 949L, 212L, 213L, 698L, 718L) */ ((/* 948L, 210L, 214L, 699L, 719L) */ ((8) << (var_1_17))) < (stepLocal_2))) {
		/* 959L, 251L, 703L, 723L) */ if (/* 954L, 230L, 231L, 704L, 724L) */ ((stepLocal_1) > (/* 953L, 229L, 235L, 708L, 728L) */ ((var_1_28) - (/* 952L, 228L, 237L, 710L, 730L) */ (abs (100u))))))) {
			/* 958L, 250L, 712L, 732L) */ var_1_26 = (
				var_1_29
			);
		}
	}


	// From: CodeObject1
	/* 298L, 73L) */ if (/* 299L, 54L, 55L) */ ((/* 300L, 52L, 56L) */ ((/* 301L, 50L, 57L) */ (min (/* 301L, 50L, 57L) */ (var_1_3) , (var_1_4)))) - (var_1_4))) <= (var_1_8))) {
		/* 306L, 72L) */ var_1_30 = (
			var_1_3
		);
	}


	// From: CodeObject2
	/* 310L, 136L) */ if (/* 311L, 87L, 88L) */ ((var_1_8) >= (/* 313L, 86L, 90L) */ (min (/* 313L, 86L, 90L) */ (var_1_3) , (var_1_4)))))) {
		/* 316L, 134L) */ if (/* 317L, 106L, 107L) */ ((/* 318L, 104L, 108L) */ ((/* 319L, 102L, 109L) */ ((var_1_4) ^ (var_1_8))) * (var_1_8))) >= (var_1_3))) {
			/* 324L, 125L) */ var_1_35 = (
				/* 327L, 124L) */ (abs (
					var_1_10
				))
			);
		} else {
			/* 329L, 133L) */ var_1_35 = (
				/* 332L, 132L) */ (abs (
					/* 333L, 131L) */ ((
						/* 334L, 129L) */ (abs (
							var_1_10
						))
					) - (
						1.0000000000000005E15f
					))
				))
			);
		}
	}


	// From: CodeObject3
	/* 370L, 156L) */ if (/* 371L, 142L, 143L) */ ((var_1_35) >= (var_1_37))) {
		/* 374L, 155L) */ var_1_38 = (
			/* 377L, 154L) */ (max (
				/* 377L, 154L) */ (
					var_1_23
				) , (
					/* 379L, 153L) */ (abs (
						var_1_4
					))
				)
			))
		);
	}


	// From: CodeObject4
	/* 382L, 163L) */ var_1_39 = (
		var_1_4
	);


	// From: CodeObject5
	/* 386L, 209L) */ if (/* 387L, 172L, 173L) */ ((/* 388L, 170L, 174L) */ (~ (/* 389L, 169L, 175L) */ (~ (var_1_4))))) <= (128))) {
		/* 392L, 187L) */ var_1_40 = (
			/* 395L, 186L) */ (abs (
				var_1_16
			))
		);
	} else {
		/* 397L, 207L) */ if (/* 398L, 190L, 191L) */ ((var_1_36) && (var_1_42))) {
			/* 401L, 202L) */ var_1_40 = (
				/* 404L, 201L) */ (abs (
					/* 405L, 200L) */ (abs (
						var_1_16
					))
				))
			);
		} else {
			/* 407L, 206L) */ var_1_40 = (
				var_1_16
			);
		}
	}


	// From: CodeObject6
	/* 411L, 246L) */ if (/* 412L, 215L, 216L) */ ((var_1_28) < (var_1_8))) {
		/* 415L, 244L) */ if (/* 416L, 226L, 227L) */ ((var_1_1) <= (/* 418L, 225L, 229L) */ ((var_1_8) / (-32))))) {
			/* 421L, 243L) */ var_1_43 = (
				/* 424L, 242L) */ (abs (
					/* 425L, 241L) */ ((
						var_1_45
					) - (
						var_1_46
					))
				))
			);
		}
	}


	// From: CodeObject7
	/* 428L, 293L) */ if (/* 429L, 256L, 257L) */ ((/* 430L, 254L, 258L) */ ((/* 431L, 252L, 259L) */ ((var_1_46) - (var_1_48))) / (-2))) < (var_1_18))) {
		/* 436L, 287L) */ if (var_1_42) {
			/* 438L, 281L) */ if (var_1_36) {
				/* 440L, 280L) */ var_1_47 = (
					var_1_4
				);
			}
		} else {
			/* 444L, 286L) */ var_1_47 = (
				var_1_46
			);
		}
	} else {
		/* 448L, 292L) */ var_1_47 = (
			var_1_4
		);
	}
}



void updateVariables(void) {
	var_1_3 = __VERIFIER_nondet_short();
	assume_abort_if_not(var_1_3 >= -1);
	assume_abort_if_not(var_1_3 <= 32767);
	var_1_4 = __VERIFIER_nondet_short();
	assume_abort_if_not(var_1_4 >= 0);
	assume_abort_if_not(var_1_4 <= 32767);
	var_1_5 = __VERIFIER_nondet_short();
	assume_abort_if_not(var_1_5 >= -32768);
	assume_abort_if_not(var_1_5 <= 32767);
	assume_abort_if_not(var_1_5 != 0);
	var_1_6 = __VERIFIER_nondet_short();
	assume_abort_if_not(var_1_6 >= -32768);
	assume_abort_if_not(var_1_6 <= 32767);
	assume_abort_if_not(var_1_6 != 0);
	var_1_7 = __VERIFIER_nondet_long();
	assume_abort_if_not(var_1_7 >= 0);
	assume_abort_if_not(var_1_7 <= 2147483646);
	var_1_10 = __VERIFIER_nondet_double();
	assume_abort_if_not((var_1_10 >= 0.0F && var_1_10 <= -1.0e-20F) || (var_1_10 <= 9223372.036854766000e+12F && var_1_10 >= 1.0e-20F ));
	var_1_11 = __VERIFIER_nondet_double();
	assume_abort_if_not((var_1_11 >= 0.0F && var_1_11 <= -1.0e-20F) || (var_1_11 <= 4611686.018427383000e+12F && var_1_11 >= 1.0e-20F ));
	var_1_12 = __VERIFIER_nondet_double();
	assume_abort_if_not((var_1_12 >= 0.0F && var_1_12 <= -1.0e-20F) || (var_1_12 <= 4611686.018427383000e+12F && var_1_12 >= 1.0e-20F ));
	var_1_14 = __VERIFIER_nondet_short();
	assume_abort_if_not(var_1_14 >= -32767);
	assume_abort_if_not(var_1_14 <= 32766);
	var_1_16 = __VERIFIER_nondet_char();
	assume_abort_if_not(var_1_16 >= -63);
	assume_abort_if_not(var_1_16 <= 63);
	var_1_17 = __VERIFIER_nondet_char();
	assume_abort_if_not(var_1_17 >= -63);
	assume_abort_if_not(var_1_17 <= 63);
	var_1_18 = __VERIFIER_nondet_char();
	assume_abort_if_not(var_1_18 >= -63);
	assume_abort_if_not(var_1_18 <= 63);
	var_1_19 = __VERIFIER_nondet_char();
	assume_abort_if_not(var_1_19 >= -127);
	assume_abort_if_not(var_1_19 <= 126);
	var_1_21 = __VERIFIER_nondet_ushort();
	assume_abort_if_not(var_1_21 >= 32767);
	assume_abort_if_not(var_1_21 <= 65535);
	var_1_23 = __VERIFIER_nondet_ushort();
	assume_abort_if_not(var_1_23 >= 0);
	assume_abort_if_not(var_1_23 <= 32767);
	var_1_24 = __VERIFIER_nondet_ushort();
	assume_abort_if_not(var_1_24 >= 0);
	assume_abort_if_not(var_1_24 <= 16384);
	var_1_25 = __VERIFIER_nondet_ushort();
	assume_abort_if_not(var_1_25 >= 0);
	assume_abort_if_not(var_1_25 <= 16383);
	var_1_28 = __VERIFIER_nondet_ulong();
	assume_abort_if_not(var_1_28 >= 2147483647);
	assume_abort_if_not(var_1_28 <= 4294967295);
	var_1_29 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_29 >= 0);
	assume_abort_if_not(var_1_29 <= 254);
	var_1_36 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_36 >= 1);
	assume_abort_if_not(var_1_36 <= 1);
	var_1_37 = __VERIFIER_nondet_float();
	assume_abort_if_not((var_1_37 >= -922337.2036854766000e+13F && var_1_37 <= -1.0e-20F) || (var_1_37 <= 9223372.036854766000e+12F && var_1_37 >= 1.0e-20F ));
	var_1_42 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_42 >= 0);
	assume_abort_if_not(var_1_42 <= 1);
	var_1_45 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_45 >= 127);
	assume_abort_if_not(var_1_45 <= 254);
	var_1_46 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_46 >= 0);
	assume_abort_if_not(var_1_46 <= 127);
	var_1_48 = __VERIFIER_nondet_char();
	assume_abort_if_not(var_1_48 >= 0);
	assume_abort_if_not(var_1_48 <= 127);
}



void updateLastVariables(void) {
	last_1_var_1_13 = var_1_13;
}

int property(void) {
	if (/* 454L, 13L, 23L, 303L, 325L, 809L, 967L, 32L) */ ((last_1_var_1_13) < (/* 457L, 12L, 25L, 305L, 327L, 808L, 970L, 31L) */ ((/* 458L, 8L, 26L, 306L, 328L, 804L, 971L, 27L) */ ((var_1_3) - (var_1_4))) / (/* 461L, 11L, 29L, 309L, 331L, 807L, 974L, 30L) */ (max (/* 461L, 11L, 29L, 309L, 331L, 807L, 974L, 30L) */ (var_1_5) , (var_1_6)))))))) {
	}
	if (/* 477L, 52L, 56L, 369L, 380L, 990L) */ ((var_1_6) > (var_1_5))) {
	}
	if (/* 503L, 97L, 104L, 477L, 490L, 1016L) */ ((var_1_4) == (/* 505L, 96L, 106L, 479L, 492L, 1018L) */ (~ (/* 506L, 95L, 107L, 480L, 493L, 1019L) */ ((var_1_5) + (var_1_1))))))) {
	}
	if (/* 516L, 126L, 132L, 551L, 575L, 1029L) */ ((var_1_14) > (/* 518L, 125L, 134L, 553L, 577L, 1031L) */ (max (/* 518L, 125L, 134L, 553L, 577L, 1031L) */ (var_1_1) , (-8)))))) {
	} else {
	}
	if (/* 539L, 167L, 175L, 624L, 637L, 1052L) */ ((/* 540L, 165L, 176L, 625L, 638L, 1053L) */ ((/* 541L, 163L, 177L, 626L, 639L, 1054L) */ ((var_1_21) - (var_1_4))) << (var_1_16))) < (var_1_8))) {
	}
	if (/* 564L, 212L, 218L, 738L, 758L, 1077L) */ ((/* 565L, 210L, 219L, 739L, 759L, 1078L) */ ((8) << (var_1_17))) < (var_1_8))) {
		if (/* 570L, 230L, 239L, 744L, 764L, 1083L) */ ((/* 571L, 225L, 240L, 745L, 765L, 1084L) */ ((5u) >> (16))) > (/* 574L, 229L, 243L, 748L, 768L, 1087L) */ ((var_1_28) - (/* 576L, 228L, 245L, 750L, 770L, 1089L) */ (abs (100u))))))) {
		}
	}
	return /* 589L) */ ((
	/* 588L) */ ((
		/* 587L) */ ((
			/* 586L) */ ((
				/* 585L) */ ((
					/* 584L) */ ((
						/* 583L) */ ((
							/* 453L, 43L, 302L, 324L, 820L, 966L, 43L) */ ((
								/* 454L, 13L, 23L, 303L, 325L, 809L, 967L, 32L) */ ((
									last_1_var_1_13
								) < (
									/* 457L, 12L, 25L, 305L, 327L, 808L, 970L, 31L) */ ((
										/* 458L, 8L, 26L, 306L, 328L, 804L, 971L, 27L) */ ((
											var_1_3
										) - (
											var_1_4
										))
									) / (
										/* 461L, 11L, 29L, 309L, 331L, 807L, 974L, 30L) */ (max (
											/* 461L, 11L, 29L, 309L, 331L, 807L, 974L, 30L) */ (
												var_1_5
											) , (
												var_1_6
											)
										))
									))
								))
							) ? (
								/* 464L, 41L, 312L, 334L, 819L, 977L, 42L) */ ((
									var_1_1
								) == (
									/* 464L, 41L, 312L, 334L, 819L, 977L, 42L) */ ((signed long int) (
										/* 467L, 40L, 315L, 337L, 818L, 980L, 41L) */ ((
											var_1_3
										) - (
											/* 469L, 39L, 317L, 339L, 817L, 982L, 40L) */ (max (
												/* 469L, 39L, 317L, 339L, 817L, 982L, 40L) */ (
													/* 470L, 37L, 318L, 340L, 815L, 983L, 38L) */ (max (
														/* 470L, 37L, 318L, 340L, 815L, 983L, 38L) */ (
															64
														) , (
															var_1_4
														)
													))
												) , (
													var_1_7
												)
											))
										))
									))
								))
							) : (
								1
							))
						) && (
							/* 476L, 65L, 368L, 379L, 989L) */ ((
								/* 477L, 52L, 56L, 369L, 380L, 990L) */ ((
									var_1_6
								) > (
									var_1_5
								))
							) ? (
								/* 480L, 63L, 372L, 383L, 993L) */ ((
									var_1_8
								) == (
									/* 480L, 63L, 372L, 383L, 993L) */ ((signed long int) (
										/* 483L, 62L, 375L, 386L, 996L) */ (abs (
											var_1_3
										))
									))
								))
							) : (
								1
							))
						))
					) && (
						/* 488L, 83L, 421L, 436L, 1001L) */ ((
							var_1_9
						) == (
							/* 488L, 83L, 421L, 436L, 1001L) */ ((double) (
								/* 491L, 82L, 424L, 439L, 1004L) */ ((
									/* 492L, 78L, 425L, 440L, 1005L) */ (min (
										/* 492L, 78L, 425L, 440L, 1005L) */ (
											var_1_10
										) , (
											/* 494L, 77L, 427L, 442L, 1007L) */ ((
												1.000000000000005E14
											) + (
												256.1
											))
										)
									))
								) - (
									/* 497L, 81L, 430L, 445L, 1010L) */ ((
										var_1_11
									) + (
										var_1_12
									))
								))
							))
						))
					))
				) && (
					/* 502L, 115L, 476L, 489L, 1015L) */ ((
						/* 503L, 97L, 104L, 477L, 490L, 1016L) */ ((
							var_1_4
						) == (
							/* 505L, 96L, 106L, 479L, 492L, 1018L) */ (~ (
								/* 506L, 95L, 107L, 480L, 493L, 1019L) */ ((
									var_1_5
								) + (
									var_1_1
								))
							))
						))
					) ? (
						/* 509L, 113L, 483L, 496L, 1022L) */ ((
							var_1_13
						) == (
							/* 509L, 113L, 483L, 496L, 1022L) */ ((signed short int) (
								var_1_14
							))
						))
					) : (
						1
					))
				))
			) && (
				/* 515L, 154L, 550L, 574L, 1028L) */ ((
					/* 516L, 126L, 132L, 551L, 575L, 1029L) */ ((
						var_1_14
					) > (
						/* 518L, 125L, 134L, 553L, 577L, 1031L) */ (max (
							/* 518L, 125L, 134L, 553L, 577L, 1031L) */ (
								var_1_1
							) , (
								-8
							)
						))
					))
				) ? (
					/* 521L, 146L, 556L, 580L, 1034L) */ ((
						var_1_15
					) == (
						/* 521L, 146L, 556L, 580L, 1034L) */ ((signed char) (
							/* 524L, 145L, 559L, 583L, 1037L) */ (min (
								/* 524L, 145L, 559L, 583L, 1037L) */ (
									/* 525L, 143L, 560L, 584L, 1038L) */ ((
										var_1_16
									) + (
										/* 527L, 142L, 562L, 586L, 1040L) */ (max (
											/* 527L, 142L, 562L, 586L, 1040L) */ (
												var_1_17
											) , (
												var_1_18
											)
										))
									))
								) , (
									var_1_19
								)
							))
						))
					))
				) : (
					/* 531L, 152L, 566L, 590L, 1044L) */ ((
						var_1_15
					) == (
						/* 531L, 152L, 566L, 590L, 1044L) */ ((signed char) (
							/* 534L, 151L, 569L, 593L, 1047L) */ (min (
								/* 534L, 151L, 569L, 593L, 1047L) */ (
									var_1_16
								) , (
									var_1_19
								)
							))
						))
					))
				))
			))
		) && (
			/* 538L, 187L, 623L, 636L, 1051L) */ ((
				/* 539L, 167L, 175L, 624L, 637L, 1052L) */ ((
					/* 540L, 165L, 176L, 625L, 638L, 1053L) */ ((
						/* 541L, 163L, 177L, 626L, 639L, 1054L) */ ((
							var_1_21
						) - (
							var_1_4
						))
					) << (
						var_1_16
					))
				) < (
					var_1_8
				))
			) ? (
				/* 546L, 185L, 631L, 644L, 1059L) */ ((
					var_1_20
				) == (
					/* 546L, 185L, 631L, 644L, 1059L) */ ((signed char) (
						var_1_16
					))
				))
			) : (
				1
			))
		))
	) && (
		/* 552L, 201L, 674L, 686L, 1065L) */ ((
			var_1_22
		) == (
			/* 552L, 201L, 674L, 686L, 1065L) */ ((unsigned short int) (
				/* 555L, 200L, 677L, 689L, 1068L) */ ((
					/* 556L, 196L, 678L, 690L, 1069L) */ (min (
						/* 556L, 196L, 678L, 690L, 1069L) */ (
							var_1_4
						) , (
							var_1_23
						)
					))
				) + (
					/* 559L, 199L, 681L, 693L, 1072L) */ ((
						var_1_24
					) + (
						var_1_25
					))
				))
			))
		))
	))
) && (
	/* 563L, 254L, 737L, 757L, 1076L) */ ((
		/* 564L, 212L, 218L, 738L, 758L, 1077L) */ ((
			/* 565L, 210L, 219L, 739L, 759L, 1078L) */ ((
				8
			) << (
				var_1_17
			))
		) < (
			var_1_8
		))
	) ? (
		/* 569L, 252L, 743L, 763L, 1082L) */ ((
			/* 570L, 230L, 239L, 744L, 764L, 1083L) */ ((
				/* 571L, 225L, 240L, 745L, 765L, 1084L) */ ((
					5u
				) >> (
					16
				))
			) > (
				/* 574L, 229L, 243L, 748L, 768L, 1087L) */ ((
					var_1_28
				) - (
					/* 576L, 228L, 245L, 750L, 770L, 1089L) */ (abs (
						100u
					))
				))
			))
		) ? (
			/* 578L, 250L, 752L, 772L, 1091L) */ ((
				var_1_26
			) == (
				/* 578L, 250L, 752L, 772L, 1091L) */ ((unsigned char) (
					var_1_29
				))
			))
		) : (
			1
		))
	) : (
		1
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
