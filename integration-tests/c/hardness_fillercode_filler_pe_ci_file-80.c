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
void reach_error(void) { __assert_fail("0", "Req1_Prop1_Batch80Filler_PE_CI.c", 13, "reach_error"); }
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
double var_1_2 = 24.25;
double var_1_3 = 128.5;
signed short int var_1_6 = -16;
signed short int var_1_7 = -2;
signed short int var_1_8 = 5;
signed short int var_1_9 = -25;
unsigned char var_1_10 = 200;
unsigned char var_1_11 = 1;
unsigned char var_1_12 = 1;
double var_1_13 = 128.375;
unsigned short int var_1_14 = 0;
float var_1_15 = 0.0;
float var_1_16 = 4.87;
float var_1_17 = 8.875;
signed char var_1_18 = -16;
double var_1_19 = 4.9;
double var_1_20 = 63.5;
double var_1_21 = 64.8;
double var_1_22 = 100.675;
double var_1_23 = 7.75;
double var_1_24 = 1.8;
float var_1_25 = 9999999999.375;
unsigned short int var_1_26 = 0;
unsigned short int var_1_27 = 10;
double var_1_29 = 9.25;
double var_1_30 = 0.0;
double var_1_31 = 127.6;
double var_1_32 = 64.75;
unsigned long int var_1_33 = 128;
unsigned long int var_1_35 = 1089279310;
unsigned long int var_1_36 = 1307137784;
unsigned long int var_1_37 = 1417807175;
unsigned long int var_1_38 = 256;
unsigned long int var_1_39 = 2;
unsigned long int var_1_40 = 2676616107;
unsigned short int var_1_41 = 5;
unsigned short int var_1_42 = 200;
unsigned short int var_1_43 = 16;
unsigned short int var_1_44 = 8;
unsigned char var_1_45 = 5;
unsigned char var_1_47 = 16;

// Calibration values

// Last'ed variables
double last_1_var_1_19 = 4.9;
double last_1_var_1_24 = 1.8;

// Additional functions


void initially(void) {
}



void step(void) {
	// From: Req1Batch80Filler_PE_CI
	/* 65L, 37L, 267L, 290L, 842L, 911L) */ if (/* 50L, 8L, 9L, 268L, 291L, 827L, 912L) */ ((/* 47L, 6L, 10L, 269L, 292L, 824L, 913L) */ ((/* 44L, 4L, 11L, 270L, 293L, 821L, 914L) */ ((var_1_2) - (var_1_3))) * (last_1_var_1_24))) < (last_1_var_1_24))) {
		/* 60L, 32L, 275L, 298L, 837L, 921L) */ var_1_1 = (
			/* 59L, 31L, 278L, 301L, 836L, 924L) */ (min (
				/* 59L, 31L, 278L, 301L, 836L, 924L) */ (
					-8
				) , (
					/* 58L, 30L, 280L, 303L, 835L, 926L) */ ((
						var_1_6
					) + (
						/* 57L, 29L, 282L, 305L, 834L, 928L) */ (min (
							/* 57L, 29L, 282L, 305L, 834L, 928L) */ (
								var_1_7
							) , (
								var_1_8
							)
						))
					))
				)
			))
		);
	} else {
		/* 64L, 36L, 285L, 308L, 841L, 931L) */ var_1_1 = (
			var_1_6
		);
	}


	// From: Req7Batch80Filler_PE_CI
	/* 1045L, 261L, 772L, 784L) */ if (/* 1046L, 246L, 247L, 773L, 785L) */ ((/* 1047L, 244L, 248L, 774L, 786L) */ ((32) + (var_1_12))) != (var_1_1))) {
		/* 1051L, 260L, 778L, 790L) */ var_1_24 = (
			var_1_21
		);
	}


	// From: Req3Batch80Filler_PE_CI
	/* 19L, 103L, 427L, 447L, 888L, 957L) */ if (var_1_11) {
		/* 6L, 78L, 429L, 449L, 875L, 959L) */ var_1_10 = (
			/* 5L, 77L, 432L, 452L, 874L, 962L) */ (min (
				/* 5L, 77L, 432L, 452L, 874L, 962L) */ (
					0
				) , (
					var_1_12
				)
			))
		);
	} else {
		/* 18L, 101L, 435L, 455L, 887L, 965L) */ if (/* 13L, 84L, 85L, 436L, 456L, 882L, 966L) */ (! (/* 12L, 83L, 86L, 437L, 457L, 881L, 967L) */ ((last_1_var_1_19) > (/* 11L, 82L, 88L, 439L, 459L, 880L, 970L) */ ((255.9) / (var_1_13))))))) {
			/* 17L, 100L, 442L, 462L, 886L, 973L) */ var_1_10 = (
				var_1_12
			);
		}
	}


	// From: Req4Batch80Filler_PE_CI
	/* 980L, 150L, 509L, 531L) */ if (/* 981L, 110L, 111L, 510L, 532L) */ (! (var_1_11))) {
		/* 983L, 148L, 512L, 534L) */ if (/* 984L, 121L, 122L, 513L, 535L) */ ((/* 985L, 119L, 123L, 514L, 536L) */ ((/* 986L, 117L, 124L, 515L, 537L) */ ((var_1_15) - (var_1_16))) - (var_1_17))) <= (var_1_13))) {
			/* 991L, 139L, 520L, 542L) */ var_1_14 = (
				var_1_10
			);
		} else {
			/* 995L, 147L, 524L, 546L) */ var_1_14 = (
				128
			);
		}
	}


	// From: Req6Batch80Filler_PE_CI
	/* 1019L, 230L, 662L, 690L) */ if (/* 1020L, 201L, 202L, 663L, 691L) */ ((var_1_12) < (/* 1022L, 200L, 204L, 665L, 693L) */ ((1) + (var_1_14))))) {
		/* 1025L, 223L, 668L, 696L) */ var_1_19 = (
			/* 1028L, 222L, 671L, 699L) */ ((
				var_1_20
			) + (
				/* 1030L, 221L, 673L, 701L) */ (max (
					/* 1030L, 221L, 673L, 701L) */ (
						/* 1031L, 217L, 674L, 702L) */ ((
							199.5
						) + (
							var_1_21
						))
					) , (
						/* 1034L, 220L, 677L, 705L) */ (max (
							/* 1034L, 220L, 677L, 705L) */ (
								var_1_22
							) , (
								var_1_23
							)
						))
					)
				))
			))
		);
	} else {
		/* 1037L, 229L, 680L, 708L) */ var_1_19 = (
			/* 1040L, 228L, 683L, 711L) */ ((
				var_1_22
			) + (
				var_1_20
			))
		);
	}


	// From: Req2Batch80Filler_PE_CI
	signed short int stepLocal_0 = var_1_8;
	/* 953L, 64L, 359L, 376L) */ if (/* 940L, 45L, 46L, 360L, 377L) */ ((stepLocal_0) >= (var_1_7))) {
		/* 946L, 57L, 363L, 380L) */ var_1_9 = (
			/* 945L, 56L, 366L, 383L) */ ((
				-256
			) + (
				var_1_6
			))
		);
	} else {
		/* 952L, 63L, 369L, 386L) */ var_1_9 = (
			/* 951L, 62L, 372L, 389L) */ ((
				var_1_7
			) + (
				var_1_6
			))
		);
	}


	// From: Req5Batch80Filler_PE_CI
	/* 1003L, 185L, 598L, 614L) */ if (/* 1004L, 166L, 167L, 599L, 615L) */ ((/* 1005L, 164L, 168L, 600L, 616L) */ ((2935136887u) - (/* 1007L, 163L, 170L, 602L, 618L) */ ((var_1_12) + (var_1_10))))) <= (var_1_14))) {
		/* 1011L, 184L, 606L, 622L) */ var_1_18 = (
			32
		);
	}


	// From: CodeObject1
	/* 313L, 113L) */ if (/* 314L, 98L, 99L) */ ((/* 315L, 96L, 100L) */ ((var_1_26) & (var_1_27))) >= (-2))) {
		/* 319L, 112L) */ var_1_25 = (
			var_1_21
		);
	}


	// From: CodeObject2
	/* 324L, 126L) */ var_1_29 = (
		/* 327L, 125L) */ ((
			/* 328L, 123L) */ ((
				8.18603254193775E18
			) - (
				/* 330L, 122L) */ ((
					var_1_30
				) - (
					var_1_31
				))
			))
		) - (
			var_1_32
		))
	);


	// From: CodeObject3
	/* 356L, 150L) */ if (var_1_11) {
		/* 358L, 149L) */ var_1_33 = (
			/* 361L, 148L) */ ((
				/* 362L, 140L) */ ((
					var_1_35
				) + (
					/* 364L, 139L) */ (min (
						/* 364L, 139L) */ (
							var_1_36
						) , (
							var_1_37
						)
					))
				))
			) - (
				/* 367L, 147L) */ ((
					/* 368L, 143L) */ ((
						var_1_26
					) + (
						var_1_27
					))
				) + (
					/* 371L, 146L) */ (min (
						/* 371L, 146L) */ (
							1000000000u
						) , (
							var_1_38
						)
					))
				))
			))
		);
	}


	// From: CodeObject4
	/* 374L, 219L) */ if (/* 375L, 162L, 163L) */ ((/* 376L, 160L, 164L) */ ((var_1_33) | (var_1_38))) > (var_1_14))) {
		/* 380L, 217L) */ if (/* 381L, 176L, 177L) */ ((var_1_21) <= (/* 383L, 175L, 179L) */ (abs (var_1_24))))) {
			/* 385L, 193L) */ var_1_39 = (
				/* 388L, 192L) */ (min (
					/* 388L, 192L) */ (
						var_1_36
					) , (
						/* 390L, 191L) */ ((
							/* 391L, 189L) */ (abs (
								var_1_40
							))
						) - (
							var_1_14
						))
					)
				))
			);
		} else {
			/* 394L, 215L) */ if (/* 395L, 197L, 198L) */ ((var_1_14) > (/* 397L, 196L, 200L) */ (abs (var_1_33))))) {
				/* 399L, 209L) */ var_1_39 = (
					var_1_38
				);
			} else {
				/* 403L, 214L) */ var_1_39 = (
					/* 406L, 213L) */ (abs (
						var_1_14
					))
				);
			}
		}
	}


	// From: CodeObject5
	/* 408L, 270L) */ if (/* 409L, 230L, 231L) */ ((/* 410L, 227L, 232L) */ (min (/* 410L, 227L, 232L) */ (/* 411L, 225L, 233L) */ ((var_1_30) * (var_1_32))) , (var_1_19)))) >= (/* 415L, 229L, 237L) */ (- (var_1_20))))) {
		/* 417L, 268L) */ if (/* 418L, 249L, 250L) */ ((var_1_35) > (var_1_40))) {
			/* 421L, 263L) */ var_1_41 = (
				/* 424L, 262L) */ ((
					8
				) + (
					/* 426L, 261L) */ (min (
						/* 426L, 261L) */ (
							var_1_42
						) , (
							var_1_43
						)
					))
				))
			);
		} else {
			/* 429L, 267L) */ var_1_41 = (
				var_1_44
			);
		}
	}


	// From: CodeObject6
	/* 433L, 301L) */ if (/* 434L, 278L, 279L) */ ((-32) < (/* 436L, 277L, 281L) */ ((var_1_42) & (var_1_14))))) {
		/* 439L, 296L) */ var_1_45 = (
			/* 442L, 295L) */ (min (
				/* 442L, 295L) */ (
					var_1_12
				) , (
					/* 444L, 294L) */ ((
						var_1_47
					) + (
						10
					))
				)
			))
		);
	} else {
		/* 447L, 300L) */ var_1_45 = (
			10
		);
	}
}



void updateVariables(void) {
	var_1_2 = __VERIFIER_nondet_double();
	assume_abort_if_not((var_1_2 >= 0.0F && var_1_2 <= -1.0e-20F) || (var_1_2 <= 9223372.036854776000e+12F && var_1_2 >= 1.0e-20F ));
	var_1_3 = __VERIFIER_nondet_double();
	assume_abort_if_not((var_1_3 >= 0.0F && var_1_3 <= -1.0e-20F) || (var_1_3 <= 9223372.036854776000e+12F && var_1_3 >= 1.0e-20F ));
	var_1_6 = __VERIFIER_nondet_short();
	assume_abort_if_not(var_1_6 >= -16383);
	assume_abort_if_not(var_1_6 <= 16383);
	var_1_7 = __VERIFIER_nondet_short();
	assume_abort_if_not(var_1_7 >= -16383);
	assume_abort_if_not(var_1_7 <= 16383);
	var_1_8 = __VERIFIER_nondet_short();
	assume_abort_if_not(var_1_8 >= -16383);
	assume_abort_if_not(var_1_8 <= 16383);
	var_1_11 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_11 >= 0);
	assume_abort_if_not(var_1_11 <= 1);
	var_1_12 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_12 >= 0);
	assume_abort_if_not(var_1_12 <= 254);
	var_1_13 = __VERIFIER_nondet_double();
	assume_abort_if_not((var_1_13 >= -922337.2036854776000e+13F && var_1_13 <= -1.0e-20F) || (var_1_13 <= 9223372.036854776000e+12F && var_1_13 >= 1.0e-20F ));
	assume_abort_if_not(var_1_13 != 0.0F);
	var_1_15 = __VERIFIER_nondet_float();
	assume_abort_if_not((var_1_15 >= 4611686.018427388000e+12F && var_1_15 <= -1.0e-20F) || (var_1_15 <= 9223372.036854776000e+12F && var_1_15 >= 1.0e-20F ));
	var_1_16 = __VERIFIER_nondet_float();
	assume_abort_if_not((var_1_16 >= 0.0F && var_1_16 <= -1.0e-20F) || (var_1_16 <= 4611686.018427388000e+12F && var_1_16 >= 1.0e-20F ));
	var_1_17 = __VERIFIER_nondet_float();
	assume_abort_if_not((var_1_17 >= 0.0F && var_1_17 <= -1.0e-20F) || (var_1_17 <= 9223372.036854776000e+12F && var_1_17 >= 1.0e-20F ));
	var_1_20 = __VERIFIER_nondet_double();
	assume_abort_if_not((var_1_20 >= -461168.6018427383000e+13F && var_1_20 <= -1.0e-20F) || (var_1_20 <= 4611686.018427383000e+12F && var_1_20 >= 1.0e-20F ));
	var_1_21 = __VERIFIER_nondet_double();
	assume_abort_if_not((var_1_21 >= -230584.3009213691400e+13F && var_1_21 <= -1.0e-20F) || (var_1_21 <= 2305843.009213691400e+12F && var_1_21 >= 1.0e-20F ));
	var_1_22 = __VERIFIER_nondet_double();
	assume_abort_if_not((var_1_22 >= -461168.6018427383000e+13F && var_1_22 <= -1.0e-20F) || (var_1_22 <= 4611686.018427383000e+12F && var_1_22 >= 1.0e-20F ));
	var_1_23 = __VERIFIER_nondet_double();
	assume_abort_if_not((var_1_23 >= -461168.6018427383000e+13F && var_1_23 <= -1.0e-20F) || (var_1_23 <= 4611686.018427383000e+12F && var_1_23 >= 1.0e-20F ));
	var_1_26 = __VERIFIER_nondet_ushort();
	assume_abort_if_not(var_1_26 >= 0);
	assume_abort_if_not(var_1_26 <= 65535);
	var_1_27 = __VERIFIER_nondet_ushort();
	assume_abort_if_not(var_1_27 >= 0);
	assume_abort_if_not(var_1_27 <= 65535);
	var_1_30 = __VERIFIER_nondet_double();
	assume_abort_if_not((var_1_30 >= 2305843.009213691400e+12F && var_1_30 <= -1.0e-20F) || (var_1_30 <= 4611686.018427383000e+12F && var_1_30 >= 1.0e-20F ));
	var_1_31 = __VERIFIER_nondet_double();
	assume_abort_if_not((var_1_31 >= 0.0F && var_1_31 <= -1.0e-20F) || (var_1_31 <= 2305843.009213691400e+12F && var_1_31 >= 1.0e-20F ));
	var_1_32 = __VERIFIER_nondet_double();
	assume_abort_if_not((var_1_32 >= 0.0F && var_1_32 <= -1.0e-20F) || (var_1_32 <= 9223372.036854766000e+12F && var_1_32 >= 1.0e-20F ));
	var_1_35 = __VERIFIER_nondet_ulong();
	assume_abort_if_not(var_1_35 >= 1073741823);
	assume_abort_if_not(var_1_35 <= 2147483647);
	var_1_36 = __VERIFIER_nondet_ulong();
	assume_abort_if_not(var_1_36 >= 1073741824);
	assume_abort_if_not(var_1_36 <= 2147483647);
	var_1_37 = __VERIFIER_nondet_ulong();
	assume_abort_if_not(var_1_37 >= 1073741824);
	assume_abort_if_not(var_1_37 <= 2147483647);
	var_1_38 = __VERIFIER_nondet_ulong();
	assume_abort_if_not(var_1_38 >= 0);
	assume_abort_if_not(var_1_38 <= 1073741823);
	var_1_40 = __VERIFIER_nondet_ulong();
	assume_abort_if_not(var_1_40 >= 2147483647);
	assume_abort_if_not(var_1_40 <= 4294967294);
	var_1_42 = __VERIFIER_nondet_ushort();
	assume_abort_if_not(var_1_42 >= 0);
	assume_abort_if_not(var_1_42 <= 32767);
	var_1_43 = __VERIFIER_nondet_ushort();
	assume_abort_if_not(var_1_43 >= 0);
	assume_abort_if_not(var_1_43 <= 32767);
	var_1_44 = __VERIFIER_nondet_ushort();
	assume_abort_if_not(var_1_44 >= 0);
	assume_abort_if_not(var_1_44 <= 65534);
	var_1_47 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_47 >= 0);
	assume_abort_if_not(var_1_47 <= 127);
}



void updateLastVariables(void) {
	last_1_var_1_19 = var_1_19;
	last_1_var_1_24 = var_1_24;
}

int property(void) {
	if (/* 452L, 8L, 16L, 314L, 337L, 852L, 1057L, 75L) */ ((/* 453L, 6L, 17L, 315L, 338L, 849L, 1058L, 72L) */ ((/* 454L, 4L, 18L, 316L, 339L, 846L, 1059L, 69L) */ ((var_1_2) - (var_1_3))) * (last_1_var_1_24))) < (last_1_var_1_24))) {
	} else {
	}
	if (/* 477L, 45L, 49L, 394L, 411L, 1082L) */ ((var_1_8) >= (var_1_7))) {
	} else {
	}
	if (var_1_11) {
	} else {
		if (/* 502L, 84L, 91L, 476L, 496L, 903L, 1107L, 34L) */ (! (/* 503L, 83L, 92L, 477L, 497L, 902L, 1108L, 33L) */ ((last_1_var_1_19) > (/* 506L, 82L, 94L, 479L, 499L, 901L, 1111L, 32L) */ ((255.9) / (var_1_13))))))) {
		}
	}
	if (/* 517L, 110L, 113L, 554L, 576L, 1122L) */ (! (var_1_11))) {
		if (/* 520L, 121L, 129L, 557L, 579L, 1125L) */ ((/* 521L, 119L, 130L, 558L, 580L, 1126L) */ ((/* 522L, 117L, 131L, 559L, 581L, 1127L) */ ((var_1_15) - (var_1_16))) - (var_1_17))) <= (var_1_13))) {
		} else {
		}
	}
	if (/* 540L, 166L, 174L, 631L, 647L, 1145L) */ ((/* 541L, 164L, 175L, 632L, 648L, 1146L) */ ((2935136887u) - (/* 543L, 163L, 177L, 634L, 650L, 1148L) */ ((var_1_12) + (var_1_10))))) <= (var_1_14))) {
	}
	if (/* 556L, 201L, 207L, 719L, 747L, 1161L) */ ((var_1_12) < (/* 558L, 200L, 209L, 721L, 749L, 1163L) */ ((1) + (var_1_14))))) {
	} else {
	}
	if (/* 582L, 246L, 252L, 797L, 809L, 1187L) */ ((/* 583L, 244L, 253L, 798L, 810L, 1188L) */ ((32) + (var_1_12))) != (var_1_1))) {
	}
	return /* 597L) */ ((
	/* 596L) */ ((
		/* 595L) */ ((
			/* 594L) */ ((
				/* 593L) */ ((
					/* 592L) */ ((
						/* 451L, 38L, 313L, 336L, 867L, 1056L, 90L) */ ((
							/* 452L, 8L, 16L, 314L, 337L, 852L, 1057L, 75L) */ ((
								/* 453L, 6L, 17L, 315L, 338L, 849L, 1058L, 72L) */ ((
									/* 454L, 4L, 18L, 316L, 339L, 846L, 1059L, 69L) */ ((
										var_1_2
									) - (
										var_1_3
									))
								) * (
									last_1_var_1_24
								))
							) < (
								last_1_var_1_24
							))
						) ? (
							/* 461L, 32L, 321L, 344L, 862L, 1066L, 85L) */ ((
								var_1_1
							) == (
								/* 461L, 32L, 321L, 344L, 862L, 1066L, 85L) */ ((signed short int) (
									/* 464L, 31L, 324L, 347L, 861L, 1069L, 84L) */ (min (
										/* 464L, 31L, 324L, 347L, 861L, 1069L, 84L) */ (
											-8
										) , (
											/* 466L, 30L, 326L, 349L, 860L, 1071L, 83L) */ ((
												var_1_6
											) + (
												/* 468L, 29L, 328L, 351L, 859L, 1073L, 82L) */ (min (
													/* 468L, 29L, 328L, 351L, 859L, 1073L, 82L) */ (
														var_1_7
													) , (
														var_1_8
													)
												))
											))
										)
									))
								))
							))
						) : (
							/* 471L, 36L, 331L, 354L, 866L, 1076L, 89L) */ ((
								var_1_1
							) == (
								/* 471L, 36L, 331L, 354L, 866L, 1076L, 89L) */ ((signed short int) (
									var_1_6
								))
							))
						))
					) && (
						/* 476L, 65L, 393L, 410L, 1081L) */ ((
							/* 477L, 45L, 49L, 394L, 411L, 1082L) */ ((
								var_1_8
							) >= (
								var_1_7
							))
						) ? (
							/* 480L, 57L, 397L, 414L, 1085L) */ ((
								var_1_9
							) == (
								/* 480L, 57L, 397L, 414L, 1085L) */ ((signed short int) (
									/* 483L, 56L, 400L, 417L, 1088L) */ ((
										-256
									) + (
										var_1_6
									))
								))
							))
						) : (
							/* 486L, 63L, 403L, 420L, 1091L) */ ((
								var_1_9
							) == (
								/* 486L, 63L, 403L, 420L, 1091L) */ ((signed short int) (
									/* 489L, 62L, 406L, 423L, 1094L) */ ((
										var_1_7
									) + (
										var_1_6
									))
								))
							))
						))
					))
				) && (
					/* 493L, 104L, 467L, 487L, 909L, 1098L, 40L) */ ((
						var_1_11
					) ? (
						/* 495L, 78L, 469L, 489L, 896L, 1100L, 27L) */ ((
							var_1_10
						) == (
							/* 495L, 78L, 469L, 489L, 896L, 1100L, 27L) */ ((unsigned char) (
								/* 498L, 77L, 472L, 492L, 895L, 1103L, 26L) */ (min (
									/* 498L, 77L, 472L, 492L, 895L, 1103L, 26L) */ (
										0
									) , (
										var_1_12
									)
								))
							))
						))
					) : (
						/* 501L, 102L, 475L, 495L, 908L, 1106L, 39L) */ ((
							/* 502L, 84L, 91L, 476L, 496L, 903L, 1107L, 34L) */ (! (
								/* 503L, 83L, 92L, 477L, 497L, 902L, 1108L, 33L) */ ((
									last_1_var_1_19
								) > (
									/* 506L, 82L, 94L, 479L, 499L, 901L, 1111L, 32L) */ ((
										255.9
									) / (
										var_1_13
									))
								))
							))
						) ? (
							/* 509L, 100L, 482L, 502L, 907L, 1114L, 38L) */ ((
								var_1_10
							) == (
								/* 509L, 100L, 482L, 502L, 907L, 1114L, 38L) */ ((unsigned char) (
									var_1_12
								))
							))
						) : (
							1
						))
					))
				))
			) && (
				/* 516L, 151L, 553L, 575L, 1121L) */ ((
					/* 517L, 110L, 113L, 554L, 576L, 1122L) */ (! (
						var_1_11
					))
				) ? (
					/* 519L, 149L, 556L, 578L, 1124L) */ ((
						/* 520L, 121L, 129L, 557L, 579L, 1125L) */ ((
							/* 521L, 119L, 130L, 558L, 580L, 1126L) */ ((
								/* 522L, 117L, 131L, 559L, 581L, 1127L) */ ((
									var_1_15
								) - (
									var_1_16
								))
							) - (
								var_1_17
							))
						) <= (
							var_1_13
						))
					) ? (
						/* 527L, 139L, 564L, 586L, 1132L) */ ((
							var_1_14
						) == (
							/* 527L, 139L, 564L, 586L, 1132L) */ ((unsigned short int) (
								var_1_10
							))
						))
					) : (
						/* 531L, 147L, 568L, 590L, 1136L) */ ((
							var_1_14
						) == (
							/* 531L, 147L, 568L, 590L, 1136L) */ ((unsigned short int) (
								128
							))
						))
					))
				) : (
					1
				))
			))
		) && (
			/* 539L, 186L, 630L, 646L, 1144L) */ ((
				/* 540L, 166L, 174L, 631L, 647L, 1145L) */ ((
					/* 541L, 164L, 175L, 632L, 648L, 1146L) */ ((
						2935136887u
					) - (
						/* 543L, 163L, 177L, 634L, 650L, 1148L) */ ((
							var_1_12
						) + (
							var_1_10
						))
					))
				) <= (
					var_1_14
				))
			) ? (
				/* 547L, 184L, 638L, 654L, 1152L) */ ((
					var_1_18
				) == (
					/* 547L, 184L, 638L, 654L, 1152L) */ ((signed char) (
						32
					))
				))
			) : (
				1
			))
		))
	) && (
		/* 555L, 231L, 718L, 746L, 1160L) */ ((
			/* 556L, 201L, 207L, 719L, 747L, 1161L) */ ((
				var_1_12
			) < (
				/* 558L, 200L, 209L, 721L, 749L, 1163L) */ ((
					1
				) + (
					var_1_14
				))
			))
		) ? (
			/* 561L, 223L, 724L, 752L, 1166L) */ ((
				var_1_19
			) == (
				/* 561L, 223L, 724L, 752L, 1166L) */ ((double) (
					/* 564L, 222L, 727L, 755L, 1169L) */ ((
						var_1_20
					) + (
						/* 566L, 221L, 729L, 757L, 1171L) */ (max (
							/* 566L, 221L, 729L, 757L, 1171L) */ (
								/* 567L, 217L, 730L, 758L, 1172L) */ ((
									199.5
								) + (
									var_1_21
								))
							) , (
								/* 570L, 220L, 733L, 761L, 1175L) */ (max (
									/* 570L, 220L, 733L, 761L, 1175L) */ (
										var_1_22
									) , (
										var_1_23
									)
								))
							)
						))
					))
				))
			))
		) : (
			/* 573L, 229L, 736L, 764L, 1178L) */ ((
				var_1_19
			) == (
				/* 573L, 229L, 736L, 764L, 1178L) */ ((double) (
					/* 576L, 228L, 739L, 767L, 1181L) */ ((
						var_1_22
					) + (
						var_1_20
					))
				))
			))
		))
	))
) && (
	/* 581L, 262L, 796L, 808L, 1186L) */ ((
		/* 582L, 246L, 252L, 797L, 809L, 1187L) */ ((
			/* 583L, 244L, 253L, 798L, 810L, 1188L) */ ((
				32
			) + (
				var_1_12
			))
		) != (
			var_1_1
		))
	) ? (
		/* 587L, 260L, 802L, 814L, 1192L) */ ((
			var_1_24
		) == (
			/* 587L, 260L, 802L, 814L, 1192L) */ ((double) (
				var_1_21
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
