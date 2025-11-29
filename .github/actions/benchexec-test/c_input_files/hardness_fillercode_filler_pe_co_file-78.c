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
void reach_error(void) { __assert_fail("0", "Req1_Prop1_Batch78Filler_PE_CO.c", 13, "reach_error"); }
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
signed long int var_1_1 = -4;
signed long int var_1_2 = 0;
unsigned char var_1_3 = 64;
unsigned char var_1_4 = 0;
unsigned char var_1_5 = 2;
unsigned short int var_1_6 = 10;
unsigned short int var_1_7 = 8;
double var_1_8 = 1.875;
signed long int var_1_9 = -4;
double var_1_10 = 63.5;
double var_1_11 = 255.375;
double var_1_12 = 999999999.525;
double var_1_13 = 63.75;
double var_1_14 = 0.625;
unsigned short int var_1_15 = 5;
signed char var_1_16 = 4;
signed char var_1_17 = 0;
signed char var_1_18 = -2;
signed char var_1_19 = 1;
unsigned short int var_1_20 = 50;
unsigned short int var_1_21 = 0;
unsigned char var_1_22 = 2;
unsigned char var_1_23 = 32;
unsigned short int var_1_24 = 8;
unsigned short int var_1_26 = 26914;
unsigned short int var_1_27 = 26182;
unsigned char var_1_28 = 5;
unsigned char var_1_29 = 50;
unsigned char var_1_30 = 10;
signed long int var_1_31 = -32;
signed long int var_1_32 = 16;
signed char var_1_33 = -10;
signed char var_1_35 = 0;
signed char var_1_36 = -2;
signed char var_1_37 = -1;
signed char var_1_38 = 64;
signed char var_1_39 = 4;
float var_1_40 = 15.75;
float var_1_43 = 49.5;
float var_1_44 = 128.5;
float var_1_45 = 64.8;
float var_1_46 = 256.85;
float var_1_47 = 9.3;
unsigned char var_1_48 = 0;
unsigned char var_1_49 = 0;
double var_1_50 = 5.4;

// Calibration values

// Last'ed variables
signed long int last_1_var_1_1 = -4;
unsigned short int last_1_var_1_6 = 10;
unsigned short int last_1_var_1_21 = 0;

// Additional functions


void initially(void) {
}



void step(void) {
	// From: Req5Batch78Filler_PE_CO
	/* 14L, 163L, 550L, 565L, 775L, 885L) */ if (/* 4L, 146L, 147L, 551L, 566L, 765L, 886L) */ ((/* 1L, 144L, 148L, 552L, 567L, 762L, 887L) */ (abs (var_1_4))) > (last_1_var_1_1))) {
		/* 13L, 162L, 555L, 570L, 774L, 891L) */ var_1_15 = (
			/* 12L, 161L, 558L, 573L, 773L, 894L) */ (max (
				/* 12L, 161L, 558L, 573L, 773L, 894L) */ (
					last_1_var_1_21
				) , (
					/* 11L, 160L, 560L, 575L, 772L, 897L) */ ((
						var_1_5
					) + (
						var_1_4
					))
				)
			))
		);
	}


	// From: Req1Batch78Filler_PE_CO
	/* 796L, 6L, 238L, 245L) */ var_1_1 = (
		/* 799L, 5L, 241L, 248L) */ (abs (
			var_1_2
		))
	);


	// From: Req2Batch78Filler_PE_CO
	signed long int stepLocal_0 = var_1_1;
	/* 813L, 28L, 265L, 276L) */ if (/* 806L, 15L, 16L, 266L, 277L) */ ((stepLocal_0) < (var_1_2))) {
		/* 812L, 27L, 269L, 280L) */ var_1_3 = (
			/* 811L, 26L, 272L, 283L) */ (max (
				/* 811L, 26L, 272L, 283L) */ (
					var_1_4
				) , (
					var_1_5
				)
			))
		);
	}


	// From: Req3Batch78Filler_PE_CO
	signed long int stepLocal_2 = -256;
	unsigned char stepLocal_1 = var_1_5;
	/* 847L, 75L, 309L, 337L) */ if (/* 826L, 38L, 39L, 310L, 338L) */ ((/* 825L, 36L, 40L, 311L, 339L) */ ((var_1_2) ^ (var_1_1))) < (stepLocal_2))) {
		/* 838L, 59L, 315L, 343L) */ var_1_6 = (
			/* 837L, 58L, 318L, 346L) */ (abs (
				/* 836L, 57L, 319L, 347L) */ (max (
					/* 836L, 57L, 319L, 347L) */ (
						/* 831L, 53L, 320L, 348L) */ (max (
							/* 831L, 53L, 320L, 348L) */ (
								var_1_5
							) , (
								var_1_4
							)
						))
					) , (
						/* 835L, 56L, 323L, 351L) */ ((
							last_1_var_1_6
						) + (
							var_1_7
						))
					)
				))
			))
		);
	} else {
		/* 846L, 73L, 327L, 355L) */ if (/* 840L, 62L, 63L, 328L, 356L) */ ((stepLocal_1) <= (50))) {
			/* 845L, 72L, 331L, 359L) */ var_1_6 = (
				last_1_var_1_6
			);
		}
	}


	// From: Req4Batch78Filler_PE_CO
	/* 853L, 135L, 422L, 454L) */ if (/* 854L, 87L, 88L, 423L, 455L) */ ((var_1_1) < (/* 856L, 86L, 90L, 425L, 457L) */ ((var_1_5) % (/* 858L, 85L, 92L, 427L, 459L) */ (max (/* 858L, 85L, 92L, 427L, 459L) */ (32) , (var_1_9)))))))) {
		/* 861L, 113L, 430L, 462L) */ var_1_8 = (
			/* 864L, 112L, 433L, 465L) */ ((
				/* 865L, 108L, 434L, 466L) */ ((
					/* 866L, 106L, 435L, 467L) */ (max (
						/* 866L, 106L, 435L, 467L) */ (
							var_1_10
						) , (
							var_1_11
						)
					))
				) - (
					var_1_12
				))
			) + (
				/* 870L, 111L, 439L, 471L) */ ((
					var_1_13
				) - (
					var_1_14
				))
			))
		);
	} else {
		/* 873L, 133L, 442L, 474L) */ if (/* 874L, 118L, 119L, 443L, 475L) */ ((var_1_13) <= (/* 876L, 117L, 121L, 445L, 477L) */ ((var_1_14) + (var_1_11))))) {
			/* 879L, 132L, 448L, 480L) */ var_1_8 = (
				var_1_12
			);
		}
	}


	// From: Req6Batch78Filler_PE_CO
	/* 902L, 179L, 610L, 621L) */ var_1_16 = (
		/* 905L, 178L, 613L, 624L) */ ((
			var_1_17
		) + (
			/* 907L, 177L, 615L, 626L) */ ((
				var_1_18
			) + (
				/* 909L, 176L, 617L, 628L) */ (abs (
					var_1_19
				))
			))
		))
	);


	// From: Req8Batch78Filler_PE_CO
	signed long int stepLocal_3 = /* 923L, 207L, 211L, 696L, 713L) */ ((/* 924L, 203L, 212L, 697L, 714L) */ ((var_1_2) * (var_1_17))) & (/* 927L, 206L, 215L, 700L, 717L) */ ((var_1_6) * (var_1_18))));
	/* 939L, 233L, 693L, 710L) */ if (/* 932L, 208L, 209L, 694L, 711L) */ ((var_1_15) == (stepLocal_3))) {
		/* 938L, 232L, 703L, 720L) */ var_1_21 = (
			/* 937L, 231L, 706L, 723L) */ ((
				var_1_4
			) + (
				128
			))
		);
	}


	// From: Req7Batch78Filler_PE_CO
	/* 913L, 193L, 654L, 664L) */ var_1_20 = (
		/* 916L, 192L, 657L, 667L) */ (max (
			/* 916L, 192L, 657L, 667L) */ (
				/* 917L, 190L, 658L, 668L) */ ((
					var_1_5
				) + (
					var_1_21
				))
			) , (
				var_1_4
			)
		))
	);


	// From: CodeObject1
	/* 250L, 39L) */ var_1_22 = (
		var_1_23
	);


	// From: CodeObject2
	/* 254L, 67L) */ if (/* 255L, 48L, 49L) */ ((/* 256L, 46L, 50L) */ (min (/* 256L, 46L, 50L) */ (var_1_15) , (var_1_23)))) >= (var_1_1))) {
		/* 260L, 66L) */ var_1_24 = (
			/* 263L, 65L) */ ((
				/* 264L, 63L) */ ((
					var_1_26
				) + (
					var_1_27
				))
			) - (
				var_1_23
			))
		);
	}


	// From: CodeObject3
	/* 268L, 90L) */ if (/* 269L, 73L, 74L) */ ((var_1_27) > (0))) {
		/* 272L, 89L) */ var_1_28 = (
			/* 275L, 88L) */ (min (
				/* 275L, 88L) */ (
					/* 276L, 86L) */ (max (
						/* 276L, 86L) */ (
							/* 277L, 84L) */ ((
								var_1_29
							) + (
								var_1_30
							))
						) , (
							var_1_23
						)
					))
				) , (
					0
				)
			))
		);
	}


	// From: CodeObject4
	/* 282L, 118L) */ if (/* 283L, 99L, 100L) */ ((var_1_26) != (/* 285L, 98L, 102L) */ ((var_1_30) + (var_1_29))))) {
		/* 288L, 117L) */ var_1_31 = (
			/* 291L, 116L) */ (abs (
				/* 292L, 115L) */ ((
					var_1_29
				) + (
					/* 294L, 114L) */ (abs (
						32
					))
				))
			))
		);
	}


	// From: CodeObject5
	/* 296L, 161L) */ if (/* 297L, 124L, 125L) */ ((var_1_26) > (100))) {
		/* 300L, 159L) */ if (/* 301L, 136L, 137L) */ ((/* 302L, 134L, 138L) */ ((/* 303L, 132L, 139L) */ (abs (var_1_27))) ^ (var_1_26))) > (var_1_1))) {
			/* 307L, 154L) */ var_1_32 = (
				/* 310L, 153L) */ ((
					var_1_29
				) - (
					var_1_26
				))
			);
		} else {
			/* 313L, 158L) */ var_1_32 = (
				var_1_21
			);
		}
	}


	// From: CodeObject6
	/* 317L, 197L) */ if (/* 318L, 171L, 172L) */ ((var_1_1) < (/* 320L, 170L, 174L) */ ((var_1_26) + (var_1_1))))) {
		/* 323L, 188L) */ var_1_33 = (
			/* 326L, 187L) */ (abs (
				/* 327L, 186L) */ (min (
					/* 327L, 186L) */ (
						var_1_35
					) , (
						var_1_36
					)
				))
			))
		);
	} else {
		/* 330L, 196L) */ var_1_33 = (
			/* 333L, 195L) */ ((
				var_1_37
			) - (
				/* 335L, 194L) */ ((
					var_1_38
				) - (
					var_1_39
				))
			))
		);
	}


	// From: CodeObject7
	/* 338L, 231L) */ if (/* 339L, 205L, 206L) */ ((/* 340L, 203L, 207L) */ ((10.125) * (var_1_8))) < (var_1_8))) {
		/* 344L, 230L) */ var_1_40 = (
			/* 347L, 229L) */ ((
				/* 348L, 223L) */ (min (
					/* 348L, 223L) */ (
						/* 349L, 219L) */ (abs (
							var_1_43
						))
					) , (
						/* 351L, 222L) */ (min (
							/* 351L, 222L) */ (
								var_1_44
							) , (
								31.7f
							)
						))
					)
				))
			) + (
				/* 354L, 228L) */ (min (
					/* 354L, 228L) */ (
						/* 355L, 226L) */ (min (
							/* 355L, 226L) */ (
								var_1_45
							) , (
								var_1_46
							)
						))
					) , (
						var_1_47
					)
				))
			))
		);
	}


	// From: CodeObject8
	/* 360L, 238L) */ var_1_48 = (
		var_1_49
	);


	// From: CodeObject9
	/* 365L, 246L) */ var_1_50 = (
		1.4
	);
}



void updateVariables(void) {
	var_1_2 = __VERIFIER_nondet_long();
	assume_abort_if_not(var_1_2 >= -2147483646);
	assume_abort_if_not(var_1_2 <= 2147483646);
	var_1_4 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_4 >= 0);
	assume_abort_if_not(var_1_4 <= 254);
	var_1_5 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_5 >= 0);
	assume_abort_if_not(var_1_5 <= 254);
	var_1_7 = __VERIFIER_nondet_ushort();
	assume_abort_if_not(var_1_7 >= 0);
	assume_abort_if_not(var_1_7 <= 32767);
	var_1_9 = __VERIFIER_nondet_long();
	assume_abort_if_not(var_1_9 >= -2147483648);
	assume_abort_if_not(var_1_9 <= 2147483647);
	assume_abort_if_not(var_1_9 != 0);
	var_1_10 = __VERIFIER_nondet_double();
	assume_abort_if_not((var_1_10 >= 0.0F && var_1_10 <= -1.0e-20F) || (var_1_10 <= 4611686.018427383000e+12F && var_1_10 >= 1.0e-20F ));
	var_1_11 = __VERIFIER_nondet_double();
	assume_abort_if_not((var_1_11 >= 0.0F && var_1_11 <= -1.0e-20F) || (var_1_11 <= 4611686.018427383000e+12F && var_1_11 >= 1.0e-20F ));
	var_1_12 = __VERIFIER_nondet_double();
	assume_abort_if_not((var_1_12 >= 0.0F && var_1_12 <= -1.0e-20F) || (var_1_12 <= 4611686.018427383000e+12F && var_1_12 >= 1.0e-20F ));
	var_1_13 = __VERIFIER_nondet_double();
	assume_abort_if_not((var_1_13 >= 0.0F && var_1_13 <= -1.0e-20F) || (var_1_13 <= 4611686.018427383000e+12F && var_1_13 >= 1.0e-20F ));
	var_1_14 = __VERIFIER_nondet_double();
	assume_abort_if_not((var_1_14 >= 0.0F && var_1_14 <= -1.0e-20F) || (var_1_14 <= 4611686.018427383000e+12F && var_1_14 >= 1.0e-20F ));
	var_1_17 = __VERIFIER_nondet_char();
	assume_abort_if_not(var_1_17 >= -63);
	assume_abort_if_not(var_1_17 <= 63);
	var_1_18 = __VERIFIER_nondet_char();
	assume_abort_if_not(var_1_18 >= -31);
	assume_abort_if_not(var_1_18 <= 32);
	var_1_19 = __VERIFIER_nondet_char();
	assume_abort_if_not(var_1_19 >= -31);
	assume_abort_if_not(var_1_19 <= 31);
	var_1_23 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_23 >= 0);
	assume_abort_if_not(var_1_23 <= 254);
	var_1_26 = __VERIFIER_nondet_ushort();
	assume_abort_if_not(var_1_26 >= 16383);
	assume_abort_if_not(var_1_26 <= 32767);
	var_1_27 = __VERIFIER_nondet_ushort();
	assume_abort_if_not(var_1_27 >= 16384);
	assume_abort_if_not(var_1_27 <= 32767);
	var_1_29 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_29 >= 0);
	assume_abort_if_not(var_1_29 <= 127);
	var_1_30 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_30 >= 0);
	assume_abort_if_not(var_1_30 <= 127);
	var_1_35 = __VERIFIER_nondet_char();
	assume_abort_if_not(var_1_35 >= -126);
	assume_abort_if_not(var_1_35 <= 126);
	var_1_36 = __VERIFIER_nondet_char();
	assume_abort_if_not(var_1_36 >= -126);
	assume_abort_if_not(var_1_36 <= 126);
	var_1_37 = __VERIFIER_nondet_char();
	assume_abort_if_not(var_1_37 >= -1);
	assume_abort_if_not(var_1_37 <= 126);
	var_1_38 = __VERIFIER_nondet_char();
	assume_abort_if_not(var_1_38 >= 63);
	assume_abort_if_not(var_1_38 <= 126);
	var_1_39 = __VERIFIER_nondet_char();
	assume_abort_if_not(var_1_39 >= 0);
	assume_abort_if_not(var_1_39 <= 63);
	var_1_43 = __VERIFIER_nondet_float();
	assume_abort_if_not((var_1_43 >= -461168.6018427383000e+13F && var_1_43 <= -1.0e-20F) || (var_1_43 <= 4611686.018427383000e+12F && var_1_43 >= 1.0e-20F ));
	var_1_44 = __VERIFIER_nondet_float();
	assume_abort_if_not((var_1_44 >= -461168.6018427383000e+13F && var_1_44 <= -1.0e-20F) || (var_1_44 <= 4611686.018427383000e+12F && var_1_44 >= 1.0e-20F ));
	var_1_45 = __VERIFIER_nondet_float();
	assume_abort_if_not((var_1_45 >= -461168.6018427383000e+13F && var_1_45 <= -1.0e-20F) || (var_1_45 <= 4611686.018427383000e+12F && var_1_45 >= 1.0e-20F ));
	var_1_46 = __VERIFIER_nondet_float();
	assume_abort_if_not((var_1_46 >= -461168.6018427383000e+13F && var_1_46 <= -1.0e-20F) || (var_1_46 <= 4611686.018427383000e+12F && var_1_46 >= 1.0e-20F ));
	var_1_47 = __VERIFIER_nondet_float();
	assume_abort_if_not((var_1_47 >= -461168.6018427383000e+13F && var_1_47 <= -1.0e-20F) || (var_1_47 <= 4611686.018427383000e+12F && var_1_47 >= 1.0e-20F ));
	var_1_49 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_49 >= 0);
	assume_abort_if_not(var_1_49 <= 0);
}



void updateLastVariables(void) {
	last_1_var_1_1 = var_1_1;
	last_1_var_1_6 = var_1_6;
	last_1_var_1_21 = var_1_21;
}

int property(void) {
	if (/* 377L, 15L, 19L, 288L, 299L, 951L) */ ((var_1_1) < (var_1_2))) {
	}
	if (/* 388L, 38L, 44L, 366L, 394L, 962L) */ ((/* 389L, 36L, 45L, 367L, 395L, 963L) */ ((var_1_2) ^ (var_1_1))) < (-256))) {
	} else {
		if (/* 406L, 62L, 66L, 384L, 412L, 980L) */ ((var_1_5) <= (50))) {
		}
	}
	if (/* 417L, 87L, 95L, 487L, 519L, 991L) */ ((var_1_1) < (/* 419L, 86L, 97L, 489L, 521L, 993L) */ ((var_1_5) % (/* 421L, 85L, 99L, 491L, 523L, 995L) */ (max (/* 421L, 85L, 99L, 491L, 523L, 995L) */ (32) , (var_1_9)))))))) {
	} else {
		if (/* 437L, 118L, 124L, 507L, 539L, 1011L) */ ((var_1_13) <= (/* 439L, 117L, 126L, 509L, 541L, 1013L) */ ((var_1_14) + (var_1_11))))) {
		}
	}
	if (/* 449L, 146L, 151L, 581L, 596L, 782L, 1023L, 21L) */ ((/* 450L, 144L, 152L, 582L, 597L, 779L, 1024L, 18L) */ (abs (var_1_4))) > (last_1_var_1_1))) {
	}
	if (/* 486L, 208L, 218L, 728L, 745L, 1060L) */ ((var_1_15) == (/* 488L, 207L, 220L, 730L, 747L, 1062L) */ ((/* 489L, 203L, 221L, 731L, 748L, 1063L) */ ((var_1_2) * (var_1_17))) & (/* 492L, 206L, 224L, 734L, 751L, 1066L) */ ((var_1_6) * (var_1_18))))))) {
	}
	return /* 508L) */ ((
	/* 507L) */ ((
		/* 506L) */ ((
			/* 505L) */ ((
				/* 504L) */ ((
					/* 503L) */ ((
						/* 502L) */ ((
							/* 370L, 6L, 252L, 259L, 944L) */ ((
								var_1_1
							) == (
								/* 370L, 6L, 252L, 259L, 944L) */ ((signed long int) (
									/* 373L, 5L, 255L, 262L, 947L) */ (abs (
										var_1_2
									))
								))
							))
						) && (
							/* 376L, 29L, 287L, 298L, 950L) */ ((
								/* 377L, 15L, 19L, 288L, 299L, 951L) */ ((
									var_1_1
								) < (
									var_1_2
								))
							) ? (
								/* 380L, 27L, 291L, 302L, 954L) */ ((
									var_1_3
								) == (
									/* 380L, 27L, 291L, 302L, 954L) */ ((unsigned char) (
										/* 383L, 26L, 294L, 305L, 957L) */ (max (
											/* 383L, 26L, 294L, 305L, 957L) */ (
												var_1_4
											) , (
												var_1_5
											)
										))
									))
								))
							) : (
								1
							))
						))
					) && (
						/* 387L, 76L, 365L, 393L, 961L) */ ((
							/* 388L, 38L, 44L, 366L, 394L, 962L) */ ((
								/* 389L, 36L, 45L, 367L, 395L, 963L) */ ((
									var_1_2
								) ^ (
									var_1_1
								))
							) < (
								-256
							))
						) ? (
							/* 393L, 59L, 371L, 399L, 967L) */ ((
								var_1_6
							) == (
								/* 393L, 59L, 371L, 399L, 967L) */ ((unsigned short int) (
									/* 396L, 58L, 374L, 402L, 970L) */ (abs (
										/* 397L, 57L, 375L, 403L, 971L) */ (max (
											/* 397L, 57L, 375L, 403L, 971L) */ (
												/* 398L, 53L, 376L, 404L, 972L) */ (max (
													/* 398L, 53L, 376L, 404L, 972L) */ (
														var_1_5
													) , (
														var_1_4
													)
												))
											) , (
												/* 401L, 56L, 379L, 407L, 975L) */ ((
													last_1_var_1_6
												) + (
													var_1_7
												))
											)
										))
									))
								))
							))
						) : (
							/* 405L, 74L, 383L, 411L, 979L) */ ((
								/* 406L, 62L, 66L, 384L, 412L, 980L) */ ((
									var_1_5
								) <= (
									50
								))
							) ? (
								/* 409L, 72L, 387L, 415L, 983L) */ ((
									var_1_6
								) == (
									/* 409L, 72L, 387L, 415L, 983L) */ ((unsigned short int) (
										last_1_var_1_6
									))
								))
							) : (
								1
							))
						))
					))
				) && (
					/* 416L, 136L, 486L, 518L, 990L) */ ((
						/* 417L, 87L, 95L, 487L, 519L, 991L) */ ((
							var_1_1
						) < (
							/* 419L, 86L, 97L, 489L, 521L, 993L) */ ((
								var_1_5
							) % (
								/* 421L, 85L, 99L, 491L, 523L, 995L) */ (max (
									/* 421L, 85L, 99L, 491L, 523L, 995L) */ (
										32
									) , (
										var_1_9
									)
								))
							))
						))
					) ? (
						/* 424L, 113L, 494L, 526L, 998L) */ ((
							var_1_8
						) == (
							/* 424L, 113L, 494L, 526L, 998L) */ ((double) (
								/* 427L, 112L, 497L, 529L, 1001L) */ ((
									/* 428L, 108L, 498L, 530L, 1002L) */ ((
										/* 429L, 106L, 499L, 531L, 1003L) */ (max (
											/* 429L, 106L, 499L, 531L, 1003L) */ (
												var_1_10
											) , (
												var_1_11
											)
										))
									) - (
										var_1_12
									))
								) + (
									/* 433L, 111L, 503L, 535L, 1007L) */ ((
										var_1_13
									) - (
										var_1_14
									))
								))
							))
						))
					) : (
						/* 436L, 134L, 506L, 538L, 1010L) */ ((
							/* 437L, 118L, 124L, 507L, 539L, 1011L) */ ((
								var_1_13
							) <= (
								/* 439L, 117L, 126L, 509L, 541L, 1013L) */ ((
									var_1_14
								) + (
									var_1_11
								))
							))
						) ? (
							/* 442L, 132L, 512L, 544L, 1016L) */ ((
								var_1_8
							) == (
								/* 442L, 132L, 512L, 544L, 1016L) */ ((double) (
									var_1_12
								))
							))
						) : (
							1
						))
					))
				))
			) && (
				/* 448L, 164L, 580L, 595L, 792L, 1022L, 31L) */ ((
					/* 449L, 146L, 151L, 581L, 596L, 782L, 1023L, 21L) */ ((
						/* 450L, 144L, 152L, 582L, 597L, 779L, 1024L, 18L) */ (abs (
							var_1_4
						))
					) > (
						last_1_var_1_1
					))
				) ? (
					/* 454L, 162L, 585L, 600L, 791L, 1028L, 30L) */ ((
						var_1_15
					) == (
						/* 454L, 162L, 585L, 600L, 791L, 1028L, 30L) */ ((unsigned short int) (
							/* 457L, 161L, 588L, 603L, 790L, 1031L, 29L) */ (max (
								/* 457L, 161L, 588L, 603L, 790L, 1031L, 29L) */ (
									last_1_var_1_21
								) , (
									/* 460L, 160L, 590L, 605L, 789L, 1034L, 28L) */ ((
										var_1_5
									) + (
										var_1_4
									))
								)
							))
						))
					))
				) : (
					1
				))
			))
		) && (
			/* 465L, 179L, 632L, 643L, 1039L) */ ((
				var_1_16
			) == (
				/* 465L, 179L, 632L, 643L, 1039L) */ ((signed char) (
					/* 468L, 178L, 635L, 646L, 1042L) */ ((
						var_1_17
					) + (
						/* 470L, 177L, 637L, 648L, 1044L) */ ((
							var_1_18
						) + (
							/* 472L, 176L, 639L, 650L, 1046L) */ (abs (
								var_1_19
							))
						))
					))
				))
			))
		))
	) && (
		/* 476L, 193L, 674L, 684L, 1050L) */ ((
			var_1_20
		) == (
			/* 476L, 193L, 674L, 684L, 1050L) */ ((unsigned short int) (
				/* 479L, 192L, 677L, 687L, 1053L) */ (max (
					/* 479L, 192L, 677L, 687L, 1053L) */ (
						/* 480L, 190L, 678L, 688L, 1054L) */ ((
							var_1_5
						) + (
							var_1_21
						))
					) , (
						var_1_4
					)
				))
			))
		))
	))
) && (
	/* 485L, 234L, 727L, 744L, 1059L) */ ((
		/* 486L, 208L, 218L, 728L, 745L, 1060L) */ ((
			var_1_15
		) == (
			/* 488L, 207L, 220L, 730L, 747L, 1062L) */ ((
				/* 489L, 203L, 221L, 731L, 748L, 1063L) */ ((
					var_1_2
				) * (
					var_1_17
				))
			) & (
				/* 492L, 206L, 224L, 734L, 751L, 1066L) */ ((
					var_1_6
				) * (
					var_1_18
				))
			))
		))
	) ? (
		/* 495L, 232L, 737L, 754L, 1069L) */ ((
			var_1_21
		) == (
			/* 495L, 232L, 737L, 754L, 1069L) */ ((unsigned short int) (
				/* 498L, 231L, 740L, 757L, 1072L) */ ((
					var_1_4
				) + (
					128
				))
			))
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
