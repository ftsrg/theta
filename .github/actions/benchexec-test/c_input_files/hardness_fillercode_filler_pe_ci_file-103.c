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
void reach_error(void) { __assert_fail("0", "Req1_Prop1_Batch103Filler_PE_CI.c", 13, "reach_error"); }
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
signed short int var_1_1 = 100;
signed long int var_1_2 = -500;
signed long int var_1_3 = -25;
signed short int var_1_6 = -64;
signed short int var_1_7 = 16;
signed short int var_1_8 = 20472;
signed short int var_1_9 = 16;
double var_1_10 = 1000000.9;
double var_1_11 = 0.0;
double var_1_12 = 0.0;
double var_1_13 = 7.25;
double var_1_14 = 64.4;
double var_1_15 = 15.625;
signed long int var_1_16 = 1000000;
signed long int var_1_17 = 128;
unsigned char var_1_18 = 100;
unsigned char var_1_20 = 1;
unsigned char var_1_21 = 10;
signed short int var_1_22 = -1;
signed char var_1_24 = -1;
unsigned short int var_1_25 = 0;
unsigned short int var_1_27 = 55769;
unsigned short int var_1_28 = 18537;
unsigned short int var_1_29 = 2;
signed short int var_1_30 = 1;
double var_1_31 = 10.4;
signed long int var_1_35 = -16;
unsigned long int var_1_38 = 25;
double var_1_39 = 127.5;
signed long int var_1_40 = 1;

// Calibration values

// Last'ed variables
double last_1_var_1_10 = 1000000.9;

// Additional functions


void initially(void) {
}



void step(void) {
	// From: Req1Batch103Filler_PE_CI
	signed long int stepLocal_0 = var_1_3;
	/* 25L, 37L, 285L, 307L, 855L, 905L) */ if (/* 5L, 4L, 5L, 286L, 308L, 835L, 885L) */ ((var_1_2) <= (stepLocal_0))) {
		/* 16L, 27L, 289L, 311L, 846L, 896L) */ if (/* 11L, 14L, 15L, 290L, 312L, 841L, 891L) */ ((/* 8L, 12L, 16L, 291L, 313L, 838L, 888L) */ (- (last_1_var_1_10))) >= (last_1_var_1_10))) {
			/* 15L, 26L, 294L, 316L, 845L, 895L) */ var_1_1 = (
				var_1_6
			);
		}
	} else {
		/* 24L, 36L, 298L, 320L, 854L, 904L) */ var_1_1 = (
			/* 23L, 35L, 301L, 323L, 853L, 903L) */ ((
				var_1_7
			) - (
				/* 22L, 34L, 303L, 325L, 852L, 902L) */ ((
					var_1_8
				) - (
					var_1_9
				))
			))
		);
	}


	// From: Req2Batch103Filler_PE_CI
	signed short int stepLocal_1 = var_1_7;
	/* 928L, 66L, 373L, 392L) */ if (/* 913L, 45L, 46L, 374L, 393L) */ ((stepLocal_1) > (var_1_1))) {
		/* 923L, 61L, 377L, 396L) */ var_1_10 = (
			/* 922L, 60L, 380L, 399L) */ ((
				/* 920L, 58L, 381L, 400L) */ ((
					var_1_11
				) - (
					/* 919L, 57L, 383L, 402L) */ ((
						var_1_12
					) - (
						var_1_13
					))
				))
			) - (
				3.25
			))
		);
	} else {
		/* 927L, 65L, 387L, 406L) */ var_1_10 = (
			var_1_11
		);
	}


	// From: Req3Batch103Filler_PE_CI
	/* 932L, 112L, 449L, 478L) */ if (/* 933L, 74L, 75L, 450L, 479L) */ ((var_1_10) > (9.99999999928E9f))) {
		/* 936L, 92L, 453L, 482L) */ var_1_14 = (
			/* 939L, 91L, 456L, 485L) */ ((
				/* 940L, 89L, 457L, 486L) */ (max (
					/* 940L, 89L, 457L, 486L) */ (
						/* 941L, 85L, 458L, 487L) */ (min (
							/* 941L, 85L, 458L, 487L) */ (
								var_1_13
							) , (
								63.75
							)
						))
					) , (
						/* 944L, 88L, 461L, 490L) */ ((
							var_1_12
						) + (
							var_1_15
						))
					)
				))
			) - (
				var_1_11
			))
		);
	} else {
		/* 948L, 110L, 465L, 494L) */ if (/* 949L, 95L, 96L, 466L, 495L) */ ((var_1_12) <= (var_1_10))) {
			/* 952L, 105L, 469L, 498L) */ var_1_14 = (
				var_1_13
			);
		} else {
			/* 956L, 109L, 473L, 502L) */ var_1_14 = (
				var_1_11
			);
		}
	}


	// From: Req4Batch103Filler_PE_CI
	/* 963L, 127L, 567L, 580L) */ var_1_16 = (
		/* 966L, 126L, 570L, 583L) */ ((
			/* 967L, 124L, 571L, 584L) */ (min (
				/* 967L, 124L, 571L, 584L) */ (
					/* 968L, 122L, 572L, 585L) */ ((
						var_1_8
					) + (
						var_1_9
					))
				) , (
					var_1_7
				)
			))
		) - (
			var_1_17
		))
	);


	// From: Req6Batch103Filler_PE_CI
	signed long int stepLocal_2 = /* 995L, 198L, 202L, 705L, 733L) */ (~ (var_1_16));
	/* 1022L, 227L, 697L, 725L) */ if (/* 1002L, 186L, 187L, 698L, 726L) */ ((var_1_10) != (/* 1001L, 185L, 189L, 700L, 728L) */ ((var_1_13) - (var_1_11))))) {
		/* 1021L, 225L, 703L, 731L) */ if (/* 1004L, 200L, 201L, 704L, 732L) */ ((stepLocal_2) > (var_1_16))) {
			/* 1012L, 216L, 708L, 736L) */ var_1_22 = (
				/* 1011L, 215L, 711L, 739L) */ ((
					/* 1009L, 213L, 712L, 740L) */ ((
						var_1_21
					) - (
						var_1_9
					))
				) + (
					var_1_16
				))
			);
		} else {
			/* 1020L, 224L, 716L, 744L) */ var_1_22 = (
				/* 1019L, 223L, 719L, 747L) */ (min (
					/* 1019L, 223L, 719L, 747L) */ (
						/* 1017L, 221L, 720L, 748L) */ (max (
							/* 1017L, 221L, 720L, 748L) */ (
								var_1_9
							) , (
								var_1_6
							)
						))
					) , (
						var_1_16
					)
				))
			);
		}
	}


	// From: Req7Batch103Filler_PE_CI
	/* 1027L, 236L, 810L, 816L) */ var_1_24 = (
		2
	);


	// From: Req5Batch103Filler_PE_CI
	/* 979L, 166L, 622L, 642L) */ if (/* 980L, 142L, 143L, 623L, 643L) */ ((var_1_8) <= (/* 982L, 141L, 145L, 625L, 645L) */ (max (/* 982L, 141L, 145L, 625L, 645L) */ (/* 983L, 139L, 146L, 626L, 646L) */ ((var_1_22) / (-500))) , (var_1_7)))))) {
		/* 987L, 164L, 630L, 650L) */ if (var_1_20) {
			/* 989L, 163L, 632L, 652L) */ var_1_18 = (
				var_1_21
			);
		}
	}


	// From: CodeObject1
	/* 312L, 86L) */ if (/* 313L, 63L, 64L) */ ((/* 314L, 59L, 65L) */ ((var_1_27) - (/* 316L, 58L, 67L) */ ((var_1_28) - (var_1_29))))) < (/* 319L, 62L, 70L) */ ((50) % (-10000))))) {
		/* 322L, 85L) */ var_1_25 = (
			var_1_29
		);
	}


	// From: CodeObject2
	/* 327L, 95L) */ var_1_30 = (
		var_1_29
	);


	// From: CodeObject3
	/* 331L, 121L) */ if (/* 332L, 102L, 103L) */ ((var_1_28) >= (var_1_1))) {
		/* 335L, 114L) */ var_1_31 = (
			/* 338L, 113L) */ ((
				var_1_13
			) - (
				var_1_12
			))
		);
	} else {
		/* 341L, 120L) */ var_1_31 = (
			/* 344L, 119L) */ ((
				var_1_13
			) + (
				-0.8
			))
		);
	}


	// From: CodeObject4
	/* 347L, 182L) */ if (/* 348L, 131L, 132L) */ ((/* 349L, 127L, 133L) */ ((16) << (10))) >= (/* 352L, 130L, 136L) */ ((var_1_17) | (var_1_29))))) {
		/* 355L, 180L) */ if (var_1_20) {
			/* 357L, 174L) */ if (/* 358L, 155L, 156L) */ ((/* 359L, 151L, 157L) */ ((2) << (var_1_16))) != (/* 362L, 154L, 160L) */ ((var_1_3) | (var_1_8))))) {
				/* 365L, 173L) */ var_1_35 = (
					var_1_16
				);
			}
		} else {
			/* 369L, 179L) */ var_1_35 = (
				var_1_16
			);
		}
	}


	// From: CodeObject5
	/* 388L, 211L) */ if (var_1_20) {
		/* 390L, 209L) */ if (/* 391L, 193L, 194L) */ ((var_1_2) == (/* 393L, 192L, 196L) */ (max (/* 393L, 192L, 196L) */ (var_1_17) , (var_1_16)))))) {
			/* 396L, 208L) */ var_1_38 = (
				/* 399L, 207L) */ (abs (
					var_1_16
				))
			);
		}
	}


	// From: CodeObject6
	/* 401L, 243L) */ if (/* 402L, 223L, 224L) */ ((var_1_17) <= (/* 404L, 222L, 226L) */ ((var_1_28) * (/* 406L, 221L, 228L) */ (max (/* 406L, 221L, 228L) */ (var_1_6) , (var_1_17)))))))) {
		/* 409L, 242L) */ var_1_39 = (
			/* 412L, 241L) */ (abs (
				9.5
			))
		);
	}


	// From: CodeObject7
	/* 415L, 307L) */ if (/* 416L, 250L, 251L) */ ((var_1_11) > (/* 418L, 249L, 253L) */ (abs (var_1_13))))) {
		/* 420L, 290L) */ if (/* 421L, 265L, 266L) */ ((/* 422L, 263L, 267L) */ (min (/* 422L, 263L, 267L) */ (var_1_13) , (/* 424L, 262L, 269L) */ ((var_1_13) / (var_1_11)))))) < (2.75))) {
			/* 428L, 289L) */ var_1_40 = (
				/* 431L, 288L) */ ((
					var_1_17
				) + (
					/* 433L, 287L) */ (min (
						/* 433L, 287L) */ (
							/* 434L, 285L) */ (max (
								/* 434L, 285L) */ (
									var_1_27
								) , (
									var_1_29
								)
							))
						) , (
							var_1_7
						)
					))
				))
			);
		}
	} else {
		/* 438L, 305L) */ if (/* 439L, 294L, 295L) */ ((var_1_16) <= (-2))) {
			/* 442L, 304L) */ var_1_40 = (
				var_1_7
			);
		}
	}
}



void updateVariables(void) {
	var_1_2 = __VERIFIER_nondet_long();
	assume_abort_if_not(var_1_2 >= -2147483648);
	assume_abort_if_not(var_1_2 <= 2147483647);
	var_1_3 = __VERIFIER_nondet_long();
	assume_abort_if_not(var_1_3 >= -2147483648);
	assume_abort_if_not(var_1_3 <= 2147483647);
	var_1_6 = __VERIFIER_nondet_short();
	assume_abort_if_not(var_1_6 >= -32767);
	assume_abort_if_not(var_1_6 <= 32766);
	var_1_7 = __VERIFIER_nondet_short();
	assume_abort_if_not(var_1_7 >= -1);
	assume_abort_if_not(var_1_7 <= 32766);
	var_1_8 = __VERIFIER_nondet_short();
	assume_abort_if_not(var_1_8 >= 16383);
	assume_abort_if_not(var_1_8 <= 32766);
	var_1_9 = __VERIFIER_nondet_short();
	assume_abort_if_not(var_1_9 >= 0);
	assume_abort_if_not(var_1_9 <= 16383);
	var_1_11 = __VERIFIER_nondet_double();
	assume_abort_if_not((var_1_11 >= 4611686.018427383000e+12F && var_1_11 <= -1.0e-20F) || (var_1_11 <= 9223372.036854766000e+12F && var_1_11 >= 1.0e-20F ));
	var_1_12 = __VERIFIER_nondet_double();
	assume_abort_if_not((var_1_12 >= 2305843.009213691400e+12F && var_1_12 <= -1.0e-20F) || (var_1_12 <= 4611686.018427383000e+12F && var_1_12 >= 1.0e-20F ));
	var_1_13 = __VERIFIER_nondet_double();
	assume_abort_if_not((var_1_13 >= 0.0F && var_1_13 <= -1.0e-20F) || (var_1_13 <= 2305843.009213691400e+12F && var_1_13 >= 1.0e-20F ));
	var_1_15 = __VERIFIER_nondet_double();
	assume_abort_if_not((var_1_15 >= 0.0F && var_1_15 <= -1.0e-20F) || (var_1_15 <= 4611686.018427383000e+12F && var_1_15 >= 1.0e-20F ));
	var_1_17 = __VERIFIER_nondet_long();
	assume_abort_if_not(var_1_17 >= 0);
	assume_abort_if_not(var_1_17 <= 2147483646);
	var_1_20 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_20 >= 0);
	assume_abort_if_not(var_1_20 <= 1);
	var_1_21 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_21 >= 0);
	assume_abort_if_not(var_1_21 <= 254);
	var_1_27 = __VERIFIER_nondet_ushort();
	assume_abort_if_not(var_1_27 >= 32767);
	assume_abort_if_not(var_1_27 <= 65535);
	var_1_28 = __VERIFIER_nondet_ushort();
	assume_abort_if_not(var_1_28 >= 16383);
	assume_abort_if_not(var_1_28 <= 32767);
	var_1_29 = __VERIFIER_nondet_ushort();
	assume_abort_if_not(var_1_29 >= 0);
	assume_abort_if_not(var_1_29 <= 16383);
}



void updateLastVariables(void) {
	last_1_var_1_10 = var_1_10;
}

int property(void) {
	if (/* 447L, 4L, 8L, 330L, 352L, 859L, 1033L, 30L) */ ((var_1_2) <= (var_1_3))) {
		if (/* 451L, 14L, 19L, 334L, 356L, 865L, 1037L, 36L) */ ((/* 452L, 12L, 20L, 335L, 357L, 862L, 1038L, 33L) */ (- (last_1_var_1_10))) >= (last_1_var_1_10))) {
		}
	} else {
	}
	if (/* 471L, 45L, 49L, 412L, 431L, 1057L) */ ((var_1_7) > (var_1_1))) {
	} else {
	}
	if (/* 490L, 74L, 78L, 508L, 537L, 1076L) */ ((var_1_10) > (9.99999999928E9f))) {
	} else {
		if (/* 506L, 95L, 99L, 524L, 553L, 1092L) */ ((var_1_12) <= (var_1_10))) {
		} else {
		}
	}
	if (/* 537L, 142L, 150L, 663L, 683L, 1123L) */ ((var_1_8) <= (/* 539L, 141L, 152L, 665L, 685L, 1125L) */ (max (/* 539L, 141L, 152L, 665L, 685L, 1125L) */ (/* 540L, 139L, 153L, 666L, 686L, 1126L) */ ((var_1_22) / (-500))) , (var_1_7)))))) {
		if (var_1_20) {
		}
	}
	if (/* 552L, 186L, 192L, 754L, 782L, 1138L) */ ((var_1_10) != (/* 554L, 185L, 194L, 756L, 784L, 1140L) */ ((var_1_13) - (var_1_11))))) {
		if (/* 558L, 200L, 205L, 760L, 788L, 1144L) */ ((/* 559L, 198L, 206L, 761L, 789L, 1145L) */ (~ (var_1_16))) > (var_1_16))) {
		} else {
		}
	}
	return /* 590L) */ ((
	/* 589L) */ ((
		/* 588L) */ ((
			/* 587L) */ ((
				/* 586L) */ ((
					/* 585L) */ ((
						/* 446L, 38L, 329L, 351L, 879L, 1032L, 50L) */ ((
							/* 447L, 4L, 8L, 330L, 352L, 859L, 1033L, 30L) */ ((
								var_1_2
							) <= (
								var_1_3
							))
						) ? (
							/* 450L, 28L, 333L, 355L, 870L, 1036L, 41L) */ ((
								/* 451L, 14L, 19L, 334L, 356L, 865L, 1037L, 36L) */ ((
									/* 452L, 12L, 20L, 335L, 357L, 862L, 1038L, 33L) */ (- (
										last_1_var_1_10
									))
								) >= (
									last_1_var_1_10
								))
							) ? (
								/* 457L, 26L, 338L, 360L, 869L, 1043L, 40L) */ ((
									var_1_1
								) == (
									/* 457L, 26L, 338L, 360L, 869L, 1043L, 40L) */ ((signed short int) (
										var_1_6
									))
								))
							) : (
								1
							))
						) : (
							/* 461L, 36L, 342L, 364L, 878L, 1047L, 49L) */ ((
								var_1_1
							) == (
								/* 461L, 36L, 342L, 364L, 878L, 1047L, 49L) */ ((signed short int) (
									/* 464L, 35L, 345L, 367L, 877L, 1050L, 48L) */ ((
										var_1_7
									) - (
										/* 466L, 34L, 347L, 369L, 876L, 1052L, 47L) */ ((
											var_1_8
										) - (
											var_1_9
										))
									))
								))
							))
						))
					) && (
						/* 470L, 67L, 411L, 430L, 1056L) */ ((
							/* 471L, 45L, 49L, 412L, 431L, 1057L) */ ((
								var_1_7
							) > (
								var_1_1
							))
						) ? (
							/* 474L, 61L, 415L, 434L, 1060L) */ ((
								var_1_10
							) == (
								/* 474L, 61L, 415L, 434L, 1060L) */ ((double) (
									/* 477L, 60L, 418L, 437L, 1063L) */ ((
										/* 478L, 58L, 419L, 438L, 1064L) */ ((
											var_1_11
										) - (
											/* 480L, 57L, 421L, 440L, 1066L) */ ((
												var_1_12
											) - (
												var_1_13
											))
										))
									) - (
										3.25
									))
								))
							))
						) : (
							/* 484L, 65L, 425L, 444L, 1070L) */ ((
								var_1_10
							) == (
								/* 484L, 65L, 425L, 444L, 1070L) */ ((double) (
									var_1_11
								))
							))
						))
					))
				) && (
					/* 489L, 113L, 507L, 536L, 1075L) */ ((
						/* 490L, 74L, 78L, 508L, 537L, 1076L) */ ((
							var_1_10
						) > (
							9.99999999928E9f
						))
					) ? (
						/* 493L, 92L, 511L, 540L, 1079L) */ ((
							var_1_14
						) == (
							/* 493L, 92L, 511L, 540L, 1079L) */ ((double) (
								/* 496L, 91L, 514L, 543L, 1082L) */ ((
									/* 497L, 89L, 515L, 544L, 1083L) */ (max (
										/* 497L, 89L, 515L, 544L, 1083L) */ (
											/* 498L, 85L, 516L, 545L, 1084L) */ (min (
												/* 498L, 85L, 516L, 545L, 1084L) */ (
													var_1_13
												) , (
													63.75
												)
											))
										) , (
											/* 501L, 88L, 519L, 548L, 1087L) */ ((
												var_1_12
											) + (
												var_1_15
											))
										)
									))
								) - (
									var_1_11
								))
							))
						))
					) : (
						/* 505L, 111L, 523L, 552L, 1091L) */ ((
							/* 506L, 95L, 99L, 524L, 553L, 1092L) */ ((
								var_1_12
							) <= (
								var_1_10
							))
						) ? (
							/* 509L, 105L, 527L, 556L, 1095L) */ ((
								var_1_14
							) == (
								/* 509L, 105L, 527L, 556L, 1095L) */ ((double) (
									var_1_13
								))
							))
						) : (
							/* 513L, 109L, 531L, 560L, 1099L) */ ((
								var_1_14
							) == (
								/* 513L, 109L, 531L, 560L, 1099L) */ ((double) (
									var_1_11
								))
							))
						))
					))
				))
			) && (
				/* 520L, 127L, 593L, 606L, 1106L) */ ((
					var_1_16
				) == (
					/* 520L, 127L, 593L, 606L, 1106L) */ ((signed long int) (
						/* 523L, 126L, 596L, 609L, 1109L) */ ((
							/* 524L, 124L, 597L, 610L, 1110L) */ (min (
								/* 524L, 124L, 597L, 610L, 1110L) */ (
									/* 525L, 122L, 598L, 611L, 1111L) */ ((
										var_1_8
									) + (
										var_1_9
									))
								) , (
									var_1_7
								)
							))
						) - (
							var_1_17
						))
					))
				))
			))
		) && (
			/* 536L, 167L, 662L, 682L, 1122L) */ ((
				/* 537L, 142L, 150L, 663L, 683L, 1123L) */ ((
					var_1_8
				) <= (
					/* 539L, 141L, 152L, 665L, 685L, 1125L) */ (max (
						/* 539L, 141L, 152L, 665L, 685L, 1125L) */ (
							/* 540L, 139L, 153L, 666L, 686L, 1126L) */ ((
								var_1_22
							) / (
								-500
							))
						) , (
							var_1_7
						)
					))
				))
			) ? (
				/* 544L, 165L, 670L, 690L, 1130L) */ ((
					var_1_20
				) ? (
					/* 546L, 163L, 672L, 692L, 1132L) */ ((
						var_1_18
					) == (
						/* 546L, 163L, 672L, 692L, 1132L) */ ((unsigned char) (
							var_1_21
						))
					))
				) : (
					1
				))
			) : (
				1
			))
		))
	) && (
		/* 551L, 228L, 753L, 781L, 1137L) */ ((
			/* 552L, 186L, 192L, 754L, 782L, 1138L) */ ((
				var_1_10
			) != (
				/* 554L, 185L, 194L, 756L, 784L, 1140L) */ ((
					var_1_13
				) - (
					var_1_11
				))
			))
		) ? (
			/* 557L, 226L, 759L, 787L, 1143L) */ ((
				/* 558L, 200L, 205L, 760L, 788L, 1144L) */ ((
					/* 559L, 198L, 206L, 761L, 789L, 1145L) */ (~ (
						var_1_16
					))
				) > (
					var_1_16
				))
			) ? (
				/* 562L, 216L, 764L, 792L, 1148L) */ ((
					var_1_22
				) == (
					/* 562L, 216L, 764L, 792L, 1148L) */ ((signed short int) (
						/* 565L, 215L, 767L, 795L, 1151L) */ ((
							/* 566L, 213L, 768L, 796L, 1152L) */ ((
								var_1_21
							) - (
								var_1_9
							))
						) + (
							var_1_16
						))
					))
				))
			) : (
				/* 570L, 224L, 772L, 800L, 1156L) */ ((
					var_1_22
				) == (
					/* 570L, 224L, 772L, 800L, 1156L) */ ((signed short int) (
						/* 573L, 223L, 775L, 803L, 1159L) */ (min (
							/* 573L, 223L, 775L, 803L, 1159L) */ (
								/* 574L, 221L, 776L, 804L, 1160L) */ (max (
									/* 574L, 221L, 776L, 804L, 1160L) */ (
										var_1_9
									) , (
										var_1_6
									)
								))
							) , (
								var_1_16
							)
						))
					))
				))
			))
		) : (
			1
		))
	))
) && (
	/* 580L, 236L, 822L, 828L, 1166L) */ ((
		var_1_24
	) == (
		/* 580L, 236L, 822L, 828L, 1166L) */ ((signed char) (
			2
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
