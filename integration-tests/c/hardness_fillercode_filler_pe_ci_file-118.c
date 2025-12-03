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
void reach_error(void) { __assert_fail("0", "Req1_Prop1_Batch118Filler_PE_CI.c", 13, "reach_error"); }
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
signed short int var_1_1 = 10;
unsigned char var_1_2 = 10;
unsigned char var_1_3 = 64;
unsigned char var_1_4 = 64;
float var_1_5 = 64.75;
float var_1_6 = -0.75;
double var_1_7 = 10.75;
unsigned char var_1_8 = 1;
unsigned char var_1_9 = 0;
double var_1_10 = 0.4;
float var_1_11 = 0.44999999999999996;
float var_1_12 = 9.5;
float var_1_13 = 15.375;
double var_1_14 = -0.375;
unsigned char var_1_15 = 0;
double var_1_16 = 1.1;
double var_1_17 = 7.5;
signed short int var_1_18 = -128;
double var_1_19 = 2.5;
unsigned short int var_1_20 = 4;
unsigned short int var_1_23 = 500;
unsigned short int var_1_24 = 1;
signed long int var_1_25 = 5;
unsigned char var_1_26 = 0;
unsigned char var_1_27 = 1;
float var_1_28 = 127.5;
float var_1_32 = 100.4;
float var_1_33 = 2.625;
float var_1_34 = 3.125;
signed long int var_1_35 = -1;
signed long int var_1_36 = 128;
signed long int var_1_37 = -2;
signed long int var_1_38 = 4;
signed char var_1_39 = 16;
signed char var_1_40 = 5;
unsigned char var_1_41 = 2;

// Calibration values

// Last'ed variables

// Additional functions


void initially(void) {
}



void step(void) {
	// From: Req1Batch118Filler_PE_CI
	/* 1027L, 5L, 351L, 357L) */ var_1_1 = (
		-5
	);


	// From: Req2Batch118Filler_PE_CI
	/* 1033L, 17L, 375L, 383L) */ var_1_2 = (
		/* 1036L, 16L, 378L, 386L) */ (max (
			/* 1036L, 16L, 378L, 386L) */ (
				var_1_3
			) , (
				var_1_4
			)
		))
	);


	// From: Req4Batch118Filler_PE_CI
	/* 1069L, 152L, 516L, 527L) */ if (/* 1070L, 141L, 142L, 517L, 528L) */ ((var_1_8) && (var_1_9))) {
		/* 1073L, 151L, 520L, 531L) */ var_1_7 = (
			var_1_6
		);
	}


	// From: Req7Batch118Filler_PE_CI
	unsigned char stepLocal_1 = /* 1120L, 248L, 252L, 709L, 732L) */ ((var_1_8) || (var_1_15));
	/* 1142L, 276L, 706L, 729L) */ if (/* 1125L, 249L, 250L, 707L, 730L) */ ((var_1_9) && (stepLocal_1))) {
		/* 1135L, 269L, 712L, 735L) */ var_1_14 = (
			/* 1134L, 268L, 715L, 738L) */ ((
				/* 1132L, 266L, 716L, 739L) */ ((
					/* 1130L, 264L, 717L, 740L) */ ((
						var_1_16
					) + (
						24.9
					))
				) + (
					var_1_17
				))
			) + (
				var_1_12
			))
		);
	} else {
		/* 1141L, 275L, 722L, 745L) */ var_1_14 = (
			/* 1140L, 274L, 725L, 748L) */ ((
				var_1_13
			) + (
				var_1_17
			))
		);
	}


	// From: Req8Batch118Filler_PE_CI
	/* 1147L, 305L, 799L, 818L) */ if (var_1_8) {
		/* 1149L, 303L, 801L, 820L) */ if (var_1_15) {
			/* 1151L, 298L, 803L, 822L) */ var_1_18 = (
				/* 1154L, 297L, 806L, 825L) */ ((
					/* 1155L, 295L, 807L, 826L) */ ((
						/* 1156L, 293L, 808L, 827L) */ (abs (
							var_1_4
						))
					) + (
						var_1_2
					))
				) + (
					var_1_3
				))
			);
		} else {
			/* 1160L, 302L, 812L, 831L) */ var_1_18 = (
				var_1_2
			);
		}
	}


	// From: Req9Batch118Filler_PE_CI
	/* 1167L, 342L, 952L, 971L) */ if (/* 1168L, 319L, 320L, 953L, 972L) */ ((/* 1169L, 317L, 321L, 954L, 973L) */ ((/* 1170L, 315L, 322L, 955L, 974L) */ ((var_1_18) + (var_1_1))) & (var_1_3))) >= (var_1_4))) {
		/* 1175L, 337L, 960L, 979L) */ var_1_19 = (
			10000.5
		);
	} else {
		/* 1179L, 341L, 964L, 983L) */ var_1_19 = (
			var_1_6
		);
	}


	// From: Req3Batch118Filler_PE_CI
	/* 1042L, 129L, 408L, 435L) */ if (/* 1043L, 28L, 29L, 409L, 436L) */ ((-2) < (/* 1045L, 27L, 31L, 411L, 438L) */ ((var_1_3) + (var_1_18))))) {
		/* 1048L, 123L, 414L, 441L) */ if (/* 1049L, 48L, 49L, 415L, 442L) */ ((/* 1050L, 46L, 50L, 416L, 443L) */ ((var_1_3) * (var_1_18))) >= (var_1_2))) {
			/* 1054L, 62L, 420L, 447L) */ var_1_5 = (
				var_1_6
			);
		} else {
			/* 1058L, 122L, 424L, 451L) */ var_1_5 = (
				49.25f
			);
		}
	} else {
		/* 1062L, 128L, 428L, 455L) */ var_1_5 = (
			var_1_6
		);
	}


	// From: Req5Batch118Filler_PE_CI
	unsigned char stepLocal_0 = /* 1079L, 173L, 179L, 560L, 581L) */ ((/* 1080L, 169L, 180L, 561L, 582L) */ ((var_1_18) - (var_1_3))) > (/* 1083L, 172L, 183L, 564L, 585L) */ ((var_1_4) + (var_1_1))));
	/* 1099L, 212L, 558L, 579L) */ if (/* 1090L, 177L, 178L, 559L, 580L) */ ((stepLocal_0) && (/* 1089L, 176L, 186L, 567L, 588L) */ ((var_1_19) > (var_1_6))))) {
		/* 1094L, 203L, 570L, 591L) */ var_1_10 = (
			var_1_6
		);
	} else {
		/* 1098L, 211L, 574L, 595L) */ var_1_10 = (
			9.25
		);
	}


	// From: Req6Batch118Filler_PE_CI
	/* 1106L, 235L, 645L, 661L) */ if (/* 1107L, 220L, 221L, 646L, 662L) */ ((var_1_14) == (var_1_6))) {
		/* 1110L, 234L, 649L, 665L) */ var_1_11 = (
			/* 1113L, 233L, 652L, 668L) */ ((
				32.7f
			) + (
				/* 1115L, 232L, 654L, 670L) */ ((
					var_1_12
				) - (
					var_1_13
				))
			))
		);
	}


	// From: CodeObject1
	/* 226L, 17L) */ if (var_1_9) {
		/* 228L, 15L) */ if (/* 229L, 6L, 7L) */ (! (var_1_9))) {
			/* 231L, 14L) */ var_1_20 = (
				var_1_23
			);
		}
	}


	// From: CodeObject2
	/* 236L, 26L) */ var_1_24 = (
		var_1_23
	);


	// From: CodeObject3
	/* 241L, 34L) */ var_1_25 = (
		var_1_20
	);


	// From: CodeObject4
	/* 245L, 76L) */ if (/* 246L, 42L, 43L) */ ((var_1_25) > (/* 248L, 41L, 45L) */ (abs (var_1_23))))) {
		/* 250L, 70L) */ if (/* 251L, 55L, 56L) */ ((var_1_25) == (/* 253L, 54L, 58L) */ ((var_1_20) & (var_1_24))))) {
			/* 256L, 69L) */ var_1_26 = (
				var_1_27
			);
		}
	} else {
		/* 260L, 75L) */ var_1_26 = (
			var_1_27
		);
	}


	// From: CodeObject5
	/* 332L, 130L) */ if (/* 333L, 82L, 83L) */ ((var_1_25) > (var_1_20))) {
		/* 336L, 118L) */ if (/* 337L, 93L, 94L) */ ((var_1_25) > (/* 339L, 92L, 96L) */ (max (/* 339L, 92L, 96L) */ (var_1_20) , (var_1_24)))))) {
			/* 342L, 109L) */ var_1_28 = (
				/* 345L, 108L) */ ((
					var_1_17
				) + (
					4.3f
				))
			);
		} else {
			/* 348L, 117L) */ var_1_28 = (
				/* 351L, 116L) */ (min (
					/* 351L, 116L) */ (
						/* 352L, 114L) */ (max (
							/* 352L, 114L) */ (
								var_1_17
							) , (
								var_1_6
							)
						))
					) , (
						var_1_6
					)
				))
			);
		}
	} else {
		/* 356L, 129L) */ var_1_28 = (
			/* 359L, 128L) */ ((
				var_1_32
			) - (
				/* 361L, 127L) */ (min (
					/* 361L, 127L) */ (
						/* 362L, 125L) */ (max (
							/* 362L, 125L) */ (
								32.8f
							) , (
								var_1_33
							)
						))
					) , (
						var_1_34
					)
				))
			))
		);
	}


	// From: CodeObject6
	/* 367L, 165L) */ if (/* 368L, 137L, 138L) */ ((var_1_13) != (/* 370L, 136L, 140L) */ (abs (var_1_13))))) {
		/* 372L, 149L) */ var_1_35 = (
			var_1_24
		);
	} else {
		/* 376L, 164L) */ var_1_35 = (
			/* 379L, 163L) */ ((
				/* 380L, 157L) */ (min (
					/* 380L, 157L) */ (
						/* 381L, 153L) */ (abs (
							var_1_20
						))
					) , (
						/* 383L, 156L) */ (max (
							/* 383L, 156L) */ (
								var_1_24
							) , (
								var_1_23
							)
						))
					)
				))
			) + (
				/* 386L, 162L) */ ((
					/* 387L, 159L) */ (abs (
						var_1_36
					))
				) - (
					/* 389L, 161L) */ (abs (
						var_1_37
					))
				))
			))
		);
	}


	// From: CodeObject7
	/* 391L, 196L) */ if (/* 392L, 177L, 178L) */ ((/* 393L, 175L, 179L) */ ((var_1_37) >> (/* 395L, 174L, 181L) */ ((var_1_39) - (var_1_40))))) <= (var_1_23))) {
		/* 399L, 195L) */ var_1_38 = (
			var_1_23
		);
	}


	// From: CodeObject8
	/* 404L, 221L) */ if (/* 405L, 202L, 203L) */ ((var_1_24) != (var_1_37))) {
		/* 408L, 219L) */ if (/* 409L, 210L, 211L) */ (! (var_1_8))) {
			/* 411L, 218L) */ var_1_41 = (
				var_1_40
			);
		}
	}
}



void updateVariables(void) {
	var_1_3 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_3 >= 0);
	assume_abort_if_not(var_1_3 <= 254);
	var_1_4 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_4 >= 0);
	assume_abort_if_not(var_1_4 <= 254);
	var_1_6 = __VERIFIER_nondet_float();
	assume_abort_if_not((var_1_6 >= -922337.2036854766000e+13F && var_1_6 <= -1.0e-20F) || (var_1_6 <= 9223372.036854766000e+12F && var_1_6 >= 1.0e-20F ));
	var_1_8 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_8 >= 0);
	assume_abort_if_not(var_1_8 <= 1);
	var_1_9 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_9 >= 0);
	assume_abort_if_not(var_1_9 <= 1);
	var_1_12 = __VERIFIER_nondet_float();
	assume_abort_if_not((var_1_12 >= 0.0F && var_1_12 <= -1.0e-20F) || (var_1_12 <= 4611686.018427383000e+12F && var_1_12 >= 1.0e-20F ));
	var_1_13 = __VERIFIER_nondet_float();
	assume_abort_if_not((var_1_13 >= 0.0F && var_1_13 <= -1.0e-20F) || (var_1_13 <= 4611686.018427383000e+12F && var_1_13 >= 1.0e-20F ));
	var_1_15 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_15 >= 0);
	assume_abort_if_not(var_1_15 <= 1);
	var_1_16 = __VERIFIER_nondet_double();
	assume_abort_if_not((var_1_16 >= -115292.1504606845700e+13F && var_1_16 <= -1.0e-20F) || (var_1_16 <= 1152921.504606845700e+12F && var_1_16 >= 1.0e-20F ));
	var_1_17 = __VERIFIER_nondet_double();
	assume_abort_if_not((var_1_17 >= -230584.3009213691400e+13F && var_1_17 <= -1.0e-20F) || (var_1_17 <= 2305843.009213691400e+12F && var_1_17 >= 1.0e-20F ));
	var_1_23 = __VERIFIER_nondet_ushort();
	assume_abort_if_not(var_1_23 >= 0);
	assume_abort_if_not(var_1_23 <= 65534);
	var_1_27 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_27 >= 1);
	assume_abort_if_not(var_1_27 <= 1);
	var_1_32 = __VERIFIER_nondet_float();
	assume_abort_if_not((var_1_32 >= 0.0F && var_1_32 <= -1.0e-20F) || (var_1_32 <= 9223372.036854766000e+12F && var_1_32 >= 1.0e-20F ));
	var_1_33 = __VERIFIER_nondet_float();
	assume_abort_if_not((var_1_33 >= 0.0F && var_1_33 <= -1.0e-20F) || (var_1_33 <= 9223372.036854766000e+12F && var_1_33 >= 1.0e-20F ));
	var_1_34 = __VERIFIER_nondet_float();
	assume_abort_if_not((var_1_34 >= 0.0F && var_1_34 <= -1.0e-20F) || (var_1_34 <= 9223372.036854766000e+12F && var_1_34 >= 1.0e-20F ));
	var_1_36 = __VERIFIER_nondet_long();
	assume_abort_if_not(var_1_36 >= -1073741823);
	assume_abort_if_not(var_1_36 <= 1073741823);
	var_1_37 = __VERIFIER_nondet_long();
	assume_abort_if_not(var_1_37 >= -1073741823);
	assume_abort_if_not(var_1_37 <= 1073741823);
	var_1_39 = __VERIFIER_nondet_char();
	assume_abort_if_not(var_1_39 >= 15);
	assume_abort_if_not(var_1_39 <= 30);
	var_1_40 = __VERIFIER_nondet_char();
	assume_abort_if_not(var_1_40 >= 0);
	assume_abort_if_not(var_1_40 <= 14);
}



void updateLastVariables(void) {
}

int property(void) {
	if (/* 432L, 28L, 34L, 463L, 490L, 1201L) */ ((-2) < (/* 434L, 27L, 36L, 465L, 492L, 1203L) */ ((var_1_3) + (var_1_18))))) {
		if (/* 438L, 48L, 54L, 469L, 496L, 1207L) */ ((/* 439L, 46L, 55L, 470L, 497L, 1208L) */ ((var_1_3) * (var_1_18))) >= (var_1_2))) {
		} else {
		}
	} else {
	}
	if (/* 459L, 141L, 145L, 539L, 550L, 1228L) */ ((var_1_8) && (var_1_9))) {
	}
	if (/* 468L, 177L, 189L, 601L, 622L, 1237L) */ ((/* 469L, 173L, 190L, 602L, 623L, 1238L) */ ((/* 470L, 169L, 191L, 603L, 624L, 1239L) */ ((var_1_18) - (var_1_3))) > (/* 473L, 172L, 194L, 606L, 627L, 1242L) */ ((var_1_4) + (var_1_1))))) && (/* 476L, 176L, 197L, 609L, 630L, 1245L) */ ((var_1_19) > (var_1_6))))) {
	} else {
	}
	if (/* 492L, 220L, 224L, 678L, 694L, 1261L) */ ((var_1_14) == (var_1_6))) {
	}
	if (/* 505L, 249L, 255L, 753L, 776L, 1274L) */ ((var_1_9) && (/* 507L, 248L, 257L, 755L, 778L, 1276L) */ ((var_1_8) || (var_1_15))))) {
	} else {
	}
	if (var_1_8) {
		if (var_1_15) {
		} else {
		}
	}
	if (/* 549L, 319L, 327L, 991L, 1010L, 1318L) */ ((/* 550L, 317L, 328L, 992L, 1011L, 1319L) */ ((/* 551L, 315L, 329L, 993L, 1012L, 1320L) */ ((var_1_18) + (var_1_1))) & (var_1_3))) >= (var_1_4))) {
	} else {
	}
	return /* 572L) */ ((
	/* 571L) */ ((
		/* 570L) */ ((
			/* 569L) */ ((
				/* 568L) */ ((
					/* 567L) */ ((
						/* 566L) */ ((
							/* 565L) */ ((
								/* 416L, 5L, 363L, 369L, 1185L) */ ((
									var_1_1
								) == (
									/* 416L, 5L, 363L, 369L, 1185L) */ ((signed short int) (
										-5
									))
								))
							) && (
								/* 422L, 17L, 391L, 399L, 1191L) */ ((
									var_1_2
								) == (
									/* 422L, 17L, 391L, 399L, 1191L) */ ((unsigned char) (
										/* 425L, 16L, 394L, 402L, 1194L) */ (max (
											/* 425L, 16L, 394L, 402L, 1194L) */ (
												var_1_3
											) , (
												var_1_4
											)
										))
									))
								))
							))
						) && (
							/* 431L, 130L, 462L, 489L, 1200L) */ ((
								/* 432L, 28L, 34L, 463L, 490L, 1201L) */ ((
									-2
								) < (
									/* 434L, 27L, 36L, 465L, 492L, 1203L) */ ((
										var_1_3
									) + (
										var_1_18
									))
								))
							) ? (
								/* 437L, 124L, 468L, 495L, 1206L) */ ((
									/* 438L, 48L, 54L, 469L, 496L, 1207L) */ ((
										/* 439L, 46L, 55L, 470L, 497L, 1208L) */ ((
											var_1_3
										) * (
											var_1_18
										))
									) >= (
										var_1_2
									))
								) ? (
									/* 443L, 62L, 474L, 501L, 1212L) */ ((
										var_1_5
									) == (
										/* 443L, 62L, 474L, 501L, 1212L) */ ((float) (
											var_1_6
										))
									))
								) : (
									/* 447L, 122L, 478L, 505L, 1216L) */ ((
										var_1_5
									) == (
										/* 447L, 122L, 478L, 505L, 1216L) */ ((float) (
											49.25f
										))
									))
								))
							) : (
								/* 451L, 128L, 482L, 509L, 1220L) */ ((
									var_1_5
								) == (
									/* 451L, 128L, 482L, 509L, 1220L) */ ((float) (
										var_1_6
									))
								))
							))
						))
					) && (
						/* 458L, 153L, 538L, 549L, 1227L) */ ((
							/* 459L, 141L, 145L, 539L, 550L, 1228L) */ ((
								var_1_8
							) && (
								var_1_9
							))
						) ? (
							/* 462L, 151L, 542L, 553L, 1231L) */ ((
								var_1_7
							) == (
								/* 462L, 151L, 542L, 553L, 1231L) */ ((double) (
									var_1_6
								))
							))
						) : (
							1
						))
					))
				) && (
					/* 467L, 213L, 600L, 621L, 1236L) */ ((
						/* 468L, 177L, 189L, 601L, 622L, 1237L) */ ((
							/* 469L, 173L, 190L, 602L, 623L, 1238L) */ ((
								/* 470L, 169L, 191L, 603L, 624L, 1239L) */ ((
									var_1_18
								) - (
									var_1_3
								))
							) > (
								/* 473L, 172L, 194L, 606L, 627L, 1242L) */ ((
									var_1_4
								) + (
									var_1_1
								))
							))
						) && (
							/* 476L, 176L, 197L, 609L, 630L, 1245L) */ ((
								var_1_19
							) > (
								var_1_6
							))
						))
					) ? (
						/* 479L, 203L, 612L, 633L, 1248L) */ ((
							var_1_10
						) == (
							/* 479L, 203L, 612L, 633L, 1248L) */ ((double) (
								var_1_6
							))
						))
					) : (
						/* 483L, 211L, 616L, 637L, 1252L) */ ((
							var_1_10
						) == (
							/* 483L, 211L, 616L, 637L, 1252L) */ ((double) (
								9.25
							))
						))
					))
				))
			) && (
				/* 491L, 236L, 677L, 693L, 1260L) */ ((
					/* 492L, 220L, 224L, 678L, 694L, 1261L) */ ((
						var_1_14
					) == (
						var_1_6
					))
				) ? (
					/* 495L, 234L, 681L, 697L, 1264L) */ ((
						var_1_11
					) == (
						/* 495L, 234L, 681L, 697L, 1264L) */ ((float) (
							/* 498L, 233L, 684L, 700L, 1267L) */ ((
								32.7f
							) + (
								/* 500L, 232L, 686L, 702L, 1269L) */ ((
									var_1_12
								) - (
									var_1_13
								))
							))
						))
					))
				) : (
					1
				))
			))
		) && (
			/* 504L, 277L, 752L, 775L, 1273L) */ ((
				/* 505L, 249L, 255L, 753L, 776L, 1274L) */ ((
					var_1_9
				) && (
					/* 507L, 248L, 257L, 755L, 778L, 1276L) */ ((
						var_1_8
					) || (
						var_1_15
					))
				))
			) ? (
				/* 510L, 269L, 758L, 781L, 1279L) */ ((
					var_1_14
				) == (
					/* 510L, 269L, 758L, 781L, 1279L) */ ((double) (
						/* 513L, 268L, 761L, 784L, 1282L) */ ((
							/* 514L, 266L, 762L, 785L, 1283L) */ ((
								/* 515L, 264L, 763L, 786L, 1284L) */ ((
									var_1_16
								) + (
									24.9
								))
							) + (
								var_1_17
							))
						) + (
							var_1_12
						))
					))
				))
			) : (
				/* 520L, 275L, 768L, 791L, 1289L) */ ((
					var_1_14
				) == (
					/* 520L, 275L, 768L, 791L, 1289L) */ ((double) (
						/* 523L, 274L, 771L, 794L, 1292L) */ ((
							var_1_13
						) + (
							var_1_17
						))
					))
				))
			))
		))
	) && (
		/* 528L, 306L, 837L, 856L, 1297L) */ ((
			var_1_8
		) ? (
			/* 530L, 304L, 839L, 858L, 1299L) */ ((
				var_1_15
			) ? (
				/* 532L, 298L, 841L, 860L, 1301L) */ ((
					var_1_18
				) == (
					/* 532L, 298L, 841L, 860L, 1301L) */ ((signed short int) (
						/* 535L, 297L, 844L, 863L, 1304L) */ ((
							/* 536L, 295L, 845L, 864L, 1305L) */ ((
								/* 537L, 293L, 846L, 865L, 1306L) */ (abs (
									var_1_4
								))
							) + (
								var_1_2
							))
						) + (
							var_1_3
						))
					))
				))
			) : (
				/* 541L, 302L, 850L, 869L, 1310L) */ ((
					var_1_18
				) == (
					/* 541L, 302L, 850L, 869L, 1310L) */ ((signed short int) (
						var_1_2
					))
				))
			))
		) : (
			1
		))
	))
) && (
	/* 548L, 343L, 990L, 1009L, 1317L) */ ((
		/* 549L, 319L, 327L, 991L, 1010L, 1318L) */ ((
			/* 550L, 317L, 328L, 992L, 1011L, 1319L) */ ((
				/* 551L, 315L, 329L, 993L, 1012L, 1320L) */ ((
					var_1_18
				) + (
					var_1_1
				))
			) & (
				var_1_3
			))
		) >= (
			var_1_4
		))
	) ? (
		/* 556L, 337L, 998L, 1017L, 1325L) */ ((
			var_1_19
		) == (
			/* 556L, 337L, 998L, 1017L, 1325L) */ ((double) (
				10000.5
			))
		))
	) : (
		/* 560L, 341L, 1002L, 1021L, 1329L) */ ((
			var_1_19
		) == (
			/* 560L, 341L, 1002L, 1021L, 1329L) */ ((double) (
				var_1_6
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
