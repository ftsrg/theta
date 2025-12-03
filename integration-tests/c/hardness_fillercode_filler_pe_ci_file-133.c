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
void reach_error(void) { __assert_fail("0", "Req1_Prop1_Batch133Filler_PE_CI.c", 13, "reach_error"); }
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
signed short int var_1_1 = -2;
unsigned char var_1_2 = 0;
unsigned char var_1_3 = 0;
unsigned char var_1_4 = 1;
signed long int var_1_5 = 64;
signed long int var_1_6 = 16;
signed short int var_1_7 = 64;
signed long int var_1_8 = -32;
signed short int var_1_9 = 256;
signed short int var_1_10 = 128;
unsigned long int var_1_11 = 0;
unsigned long int var_1_12 = 100;
unsigned char var_1_13 = 1;
unsigned char var_1_14 = 0;
unsigned char var_1_15 = 1;
unsigned char var_1_16 = 0;
signed short int var_1_17 = -25;
double var_1_18 = 1.45;
double var_1_19 = 31.2;
double var_1_20 = 1.25;
signed short int var_1_21 = -8;
unsigned char var_1_22 = 0;
signed long int var_1_23 = 256;
signed char var_1_24 = 32;
signed char var_1_25 = -8;
double var_1_26 = -0.375;
double var_1_27 = 49.4;
unsigned long int var_1_28 = 64;
signed short int var_1_34 = 5;
unsigned short int var_1_36 = 0;
unsigned short int var_1_38 = 4;
unsigned short int var_1_39 = 16;
unsigned short int var_1_40 = 4;
unsigned short int var_1_41 = 0;
unsigned long int var_1_42 = 5;
unsigned long int var_1_43 = 2293346445;
signed short int var_1_44 = 500;
unsigned long int var_1_45 = 16;
signed short int var_1_47 = 500;
signed short int var_1_48 = -64;
signed short int var_1_49 = 128;
signed short int var_1_50 = 50;
unsigned short int var_1_51 = 128;
unsigned short int var_1_52 = 50709;
unsigned short int var_1_53 = 100;
unsigned short int var_1_54 = 256;
unsigned short int var_1_55 = 64;
unsigned char var_1_56 = 0;
unsigned char var_1_57 = 0;
unsigned char var_1_58 = 0;
unsigned char var_1_59 = 0;

// Calibration values

// Last'ed variables

// Additional functions


void initially(void) {
}



void step(void) {
	// From: Req1Batch133Filler_PE_CI
	unsigned char stepLocal_1 = /* 1053L, 3L, 9L, 511L, 535L) */ (! (var_1_2));
	signed long int stepLocal_0 = var_1_5;
	/* 1075L, 51L, 509L, 533L) */ if (/* 1059L, 7L, 8L, 510L, 534L) */ ((stepLocal_1) || (/* 1058L, 6L, 11L, 513L, 537L) */ ((var_1_3) && (var_1_4))))) {
		/* 1070L, 45L, 516L, 540L) */ if (/* 1061L, 22L, 23L, 517L, 541L) */ ((stepLocal_0) == (var_1_6))) {
			/* 1065L, 32L, 520L, 544L) */ var_1_1 = (
				var_1_7
			);
		} else {
			/* 1069L, 44L, 524L, 548L) */ var_1_1 = (
				-128
			);
		}
	} else {
		/* 1074L, 50L, 528L, 552L) */ var_1_1 = (
			var_1_7
		);
	}


	// From: Req2Batch133Filler_PE_CI
	signed short int stepLocal_2 = var_1_7;
	/* 1092L, 77L, 605L, 617L) */ if (/* 1086L, 61L, 62L, 606L, 618L) */ ((stepLocal_2) > (/* 1085L, 60L, 64L, 608L, 620L) */ ((var_1_9) - (var_1_10))))) {
		/* 1091L, 76L, 611L, 623L) */ var_1_8 = (
			/* 1090L, 75L, 614L, 626L) */ (abs (
				var_1_7
			))
		);
	}


	// From: Req3Batch133Filler_PE_CI
	/* 1097L, 88L, 654L, 662L) */ var_1_11 = (
		/* 1100L, 87L, 657L, 665L) */ (min (
			/* 1100L, 87L, 657L, 665L) */ (
				var_1_10
			) , (
				var_1_12
			)
		))
	);


	// From: Req6Batch133Filler_PE_CI
	/* 1167L, 217L, 893L, 910L) */ if (/* 1168L, 194L, 195L, 894L, 911L) */ ((/* 1169L, 190L, 196L, 895L, 912L) */ (max (/* 1169L, 190L, 196L, 895L, 912L) */ (var_1_18) , (var_1_19)))) != (/* 1172L, 193L, 199L, 898L, 915L) */ ((var_1_20) * (9999.5))))) {
		/* 1175L, 216L, 901L, 918L) */ var_1_17 = (
			/* 1178L, 215L, 904L, 921L) */ ((
				/* 1179L, 213L, 905L, 922L) */ ((
					var_1_21
				) + (
					2
				))
			) + (
				-64
			))
		);
	}


	// From: Req7Batch133Filler_PE_CI
	/* 1186L, 251L, 963L, 979L) */ if (/* 1187L, 230L, 231L, 964L, 980L) */ ((/* 1188L, 226L, 232L, 965L, 981L) */ ((var_1_7) / (/* 1190L, 225L, 234L, 967L, 983L) */ (abs (var_1_23))))) > (/* 1192L, 229L, 236L, 969L, 985L) */ ((25) - (var_1_10))))) {
		/* 1195L, 250L, 972L, 988L) */ var_1_22 = (
			var_1_15
		);
	}


	// From: Req8Batch133Filler_PE_CI
	/* 1201L, 264L, 1026L, 1032L) */ var_1_24 = (
		var_1_25
	);


	// From: Req4Batch133Filler_PE_CI
	unsigned long int stepLocal_4 = var_1_11;
	signed long int stepLocal_3 = -50;
	/* 1129L, 129L, 685L, 708L) */ if (/* 1111L, 97L, 98L, 686L, 709L) */ ((var_1_11) == (stepLocal_3))) {
		/* 1124L, 123L, 689L, 712L) */ if (/* 1113L, 106L, 107L, 690L, 713L) */ ((stepLocal_4) > (10u))) {
			/* 1119L, 118L, 693L, 716L) */ var_1_13 = (
				/* 1118L, 117L, 696L, 719L) */ ((
					var_1_22
				) && (
					var_1_14
				))
			);
		} else {
			/* 1123L, 122L, 699L, 722L) */ var_1_13 = (
				var_1_15
			);
		}
	} else {
		/* 1128L, 128L, 703L, 726L) */ var_1_13 = (
			var_1_15
		);
	}


	// From: Req5Batch133Filler_PE_CI
	unsigned long int stepLocal_5 = /* 1135L, 141L, 145L, 780L, 809L) */ ((var_1_11) + (/* 1137L, 140L, 147L, 782L, 811L) */ ((var_1_11) * (10u))));
	/* 1163L, 182L, 777L, 806L) */ if (/* 1142L, 142L, 143L, 778L, 807L) */ ((var_1_12) != (stepLocal_5))) {
		/* 1151L, 165L, 785L, 814L) */ var_1_16 = (
			/* 1150L, 164L, 788L, 817L) */ ((
				/* 1147L, 161L, 789L, 818L) */ ((
					var_1_9
				) < (
					var_1_8
				))
			) && (
				/* 1149L, 163L, 792L, 821L) */ (! (
					var_1_15
				))
			))
		);
	} else {
		/* 1162L, 180L, 794L, 823L) */ if (/* 1153L, 167L, 168L, 795L, 824L) */ (! (var_1_22))) {
			/* 1157L, 175L, 797L, 826L) */ var_1_16 = (
				0
			);
		} else {
			/* 1161L, 179L, 801L, 830L) */ var_1_16 = (
				var_1_15
			);
		}
	}


	// From: CodeObject1
	/* 228L, 5L) */ var_1_26 = (
		var_1_27
	);


	// From: CodeObject2
	/* 232L, 36L) */ if (/* 233L, 16L, 17L) */ ((/* 234L, 14L, 18L) */ ((/* 235L, 12L, 19L) */ ((var_1_23) & (var_1_5))) | (var_1_11))) >= (var_1_8))) {
		/* 240L, 35L) */ var_1_28 = (
			/* 243L, 34L) */ (abs (
				var_1_12
			))
		);
	}


	// From: CodeObject3
	/* 246L, 43L) */ var_1_34 = (
		var_1_7
	);


	// From: CodeObject4
	/* 250L, 63L) */ if (var_1_15) {
		/* 252L, 62L) */ var_1_36 = (
			/* 255L, 61L) */ (min (
				/* 255L, 61L) */ (
					/* 256L, 56L) */ (min (
						/* 256L, 56L) */ (
							/* 257L, 54L) */ (abs (
								var_1_38
							))
						) , (
							var_1_39
						)
					))
				) , (
					/* 260L, 60L) */ (abs (
						/* 261L, 59L) */ ((
							var_1_40
						) + (
							var_1_41
						))
					))
				)
			))
		);
	}


	// From: CodeObject5
	/* 264L, 90L) */ if (/* 265L, 72L, 73L) */ ((var_1_6) > (-16))) {
		/* 268L, 85L) */ var_1_42 = (
			/* 271L, 84L) */ ((
				/* 272L, 82L) */ (abs (
					var_1_43
				))
			) - (
				var_1_40
			))
		);
	} else {
		/* 275L, 89L) */ var_1_42 = (
			var_1_43
		);
	}


	// From: CodeObject6
	/* 347L, 149L) */ if (/* 348L, 96L, 97L) */ ((var_1_5) <= (var_1_39))) {
		/* 351L, 143L) */ if (/* 352L, 111L, 112L) */ ((/* 353L, 109L, 113L) */ ((/* 354L, 105L, 114L) */ ((var_1_23) + (var_1_12))) ^ (/* 357L, 108L, 117L) */ ((var_1_5) / (var_1_45))))) <= (var_1_12))) {
			/* 361L, 136L) */ var_1_44 = (
				/* 364L, 135L) */ (abs (
					/* 365L, 134L) */ ((
						var_1_47
					) + (
						var_1_48
					))
				))
			);
		} else {
			/* 368L, 142L) */ var_1_44 = (
				/* 371L, 141L) */ ((
					var_1_49
				) - (
					var_1_50
				))
			);
		}
	} else {
		/* 374L, 148L) */ var_1_44 = (
			var_1_50
		);
	}


	// From: CodeObject7
	/* 380L, 166L) */ var_1_51 = (
		/* 383L, 165L) */ ((
			var_1_52
		) - (
			/* 385L, 164L) */ ((
				var_1_53
			) + (
				/* 387L, 163L) */ ((
					var_1_54
				) + (
					var_1_55
				))
			))
		))
	);


	// From: CodeObject8
	/* 422L, 225L) */ if (/* 423L, 177L, 178L) */ ((var_1_7) == (/* 425L, 176L, 180L) */ (max (/* 425L, 176L, 180L) */ (-10000) , (var_1_11)))))) {
		/* 428L, 199L) */ var_1_56 = (
			/* 431L, 198L) */ ((
				/* 432L, 194L) */ ((
					var_1_49
				) <= (
					/* 434L, 193L) */ ((
						var_1_5
					) * (
						var_1_12
					))
				))
			) || (
				/* 437L, 197L) */ ((
					var_1_57
				) && (
					var_1_58
				))
			))
		);
	} else {
		/* 440L, 223L) */ if (/* 441L, 204L, 205L) */ ((/* 442L, 202L, 206L) */ (min (/* 442L, 202L, 206L) */ (var_1_27) , (25.5f)))) > (128.25))) {
			/* 446L, 218L) */ var_1_56 = (
				var_1_59
			);
		} else {
			/* 450L, 222L) */ var_1_56 = (
				var_1_58
			);
		}
	}
}



void updateVariables(void) {
	var_1_2 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_2 >= 0);
	assume_abort_if_not(var_1_2 <= 1);
	var_1_3 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_3 >= 0);
	assume_abort_if_not(var_1_3 <= 1);
	var_1_4 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_4 >= 0);
	assume_abort_if_not(var_1_4 <= 1);
	var_1_5 = __VERIFIER_nondet_long();
	assume_abort_if_not(var_1_5 >= -2147483648);
	assume_abort_if_not(var_1_5 <= 2147483647);
	var_1_6 = __VERIFIER_nondet_long();
	assume_abort_if_not(var_1_6 >= -2147483648);
	assume_abort_if_not(var_1_6 <= 2147483647);
	var_1_7 = __VERIFIER_nondet_short();
	assume_abort_if_not(var_1_7 >= -32767);
	assume_abort_if_not(var_1_7 <= 32766);
	var_1_9 = __VERIFIER_nondet_short();
	assume_abort_if_not(var_1_9 >= -1);
	assume_abort_if_not(var_1_9 <= 32767);
	var_1_10 = __VERIFIER_nondet_short();
	assume_abort_if_not(var_1_10 >= 0);
	assume_abort_if_not(var_1_10 <= 32767);
	var_1_12 = __VERIFIER_nondet_ulong();
	assume_abort_if_not(var_1_12 >= 0);
	assume_abort_if_not(var_1_12 <= 4294967294);
	var_1_14 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_14 >= 0);
	assume_abort_if_not(var_1_14 <= 0);
	var_1_15 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_15 >= 1);
	assume_abort_if_not(var_1_15 <= 1);
	var_1_18 = __VERIFIER_nondet_double();
	assume_abort_if_not((var_1_18 >= -922337.2036854776000e+13F && var_1_18 <= -1.0e-20F) || (var_1_18 <= 9223372.036854776000e+12F && var_1_18 >= 1.0e-20F ));
	var_1_19 = __VERIFIER_nondet_double();
	assume_abort_if_not((var_1_19 >= -922337.2036854776000e+13F && var_1_19 <= -1.0e-20F) || (var_1_19 <= 9223372.036854776000e+12F && var_1_19 >= 1.0e-20F ));
	var_1_20 = __VERIFIER_nondet_double();
	assume_abort_if_not((var_1_20 >= -922337.2036854776000e+13F && var_1_20 <= -1.0e-20F) || (var_1_20 <= 9223372.036854776000e+12F && var_1_20 >= 1.0e-20F ));
	var_1_21 = __VERIFIER_nondet_short();
	assume_abort_if_not(var_1_21 >= -8191);
	assume_abort_if_not(var_1_21 <= 8192);
	var_1_23 = __VERIFIER_nondet_long();
	assume_abort_if_not(var_1_23 >= -2147483647);
	assume_abort_if_not(var_1_23 <= 2147483647);
	assume_abort_if_not(var_1_23 != 0);
	var_1_25 = __VERIFIER_nondet_char();
	assume_abort_if_not(var_1_25 >= -127);
	assume_abort_if_not(var_1_25 <= 126);
	var_1_27 = __VERIFIER_nondet_double();
	assume_abort_if_not((var_1_27 >= -922337.2036854766000e+13F && var_1_27 <= -1.0e-20F) || (var_1_27 <= 9223372.036854766000e+12F && var_1_27 >= 1.0e-20F ));
	var_1_38 = __VERIFIER_nondet_ushort();
	assume_abort_if_not(var_1_38 >= 0);
	assume_abort_if_not(var_1_38 <= 65534);
	var_1_39 = __VERIFIER_nondet_ushort();
	assume_abort_if_not(var_1_39 >= 0);
	assume_abort_if_not(var_1_39 <= 65534);
	var_1_40 = __VERIFIER_nondet_ushort();
	assume_abort_if_not(var_1_40 >= 0);
	assume_abort_if_not(var_1_40 <= 32767);
	var_1_41 = __VERIFIER_nondet_ushort();
	assume_abort_if_not(var_1_41 >= 0);
	assume_abort_if_not(var_1_41 <= 32767);
	var_1_43 = __VERIFIER_nondet_ulong();
	assume_abort_if_not(var_1_43 >= 2147483647);
	assume_abort_if_not(var_1_43 <= 4294967294);
	var_1_45 = __VERIFIER_nondet_ulong();
	assume_abort_if_not(var_1_45 >= 0);
	assume_abort_if_not(var_1_45 <= 4294967295);
	assume_abort_if_not(var_1_45 != 0);
	var_1_47 = __VERIFIER_nondet_short();
	assume_abort_if_not(var_1_47 >= -16383);
	assume_abort_if_not(var_1_47 <= 16383);
	var_1_48 = __VERIFIER_nondet_short();
	assume_abort_if_not(var_1_48 >= -16383);
	assume_abort_if_not(var_1_48 <= 16383);
	var_1_49 = __VERIFIER_nondet_short();
	assume_abort_if_not(var_1_49 >= -1);
	assume_abort_if_not(var_1_49 <= 32766);
	var_1_50 = __VERIFIER_nondet_short();
	assume_abort_if_not(var_1_50 >= 0);
	assume_abort_if_not(var_1_50 <= 32766);
	var_1_52 = __VERIFIER_nondet_ushort();
	assume_abort_if_not(var_1_52 >= 32767);
	assume_abort_if_not(var_1_52 <= 65534);
	var_1_53 = __VERIFIER_nondet_ushort();
	assume_abort_if_not(var_1_53 >= 0);
	assume_abort_if_not(var_1_53 <= 16384);
	var_1_54 = __VERIFIER_nondet_ushort();
	assume_abort_if_not(var_1_54 >= 0);
	assume_abort_if_not(var_1_54 <= 8192);
	var_1_55 = __VERIFIER_nondet_ushort();
	assume_abort_if_not(var_1_55 >= 0);
	assume_abort_if_not(var_1_55 <= 8191);
	var_1_57 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_57 >= 1);
	assume_abort_if_not(var_1_57 <= 1);
	var_1_58 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_58 >= 1);
	assume_abort_if_not(var_1_58 <= 1);
	var_1_59 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_59 >= 1);
	assume_abort_if_not(var_1_59 <= 1);
}



void updateLastVariables(void) {
}

int property(void) {
	if (/* 455L, 7L, 14L, 558L, 582L, 1207L) */ ((/* 456L, 3L, 15L, 559L, 583L, 1208L) */ (! (var_1_2))) || (/* 458L, 6L, 17L, 561L, 585L, 1210L) */ ((var_1_3) && (var_1_4))))) {
		if (/* 462L, 22L, 26L, 565L, 589L, 1214L) */ ((var_1_5) == (var_1_6))) {
		} else {
		}
	} else {
	}
	if (/* 479L, 61L, 67L, 630L, 642L, 1231L) */ ((var_1_7) > (/* 481L, 60L, 69L, 632L, 644L, 1233L) */ ((var_1_9) - (var_1_10))))) {
	}
	if (/* 499L, 97L, 101L, 732L, 755L, 1251L) */ ((var_1_11) == (-50))) {
		if (/* 503L, 106L, 110L, 736L, 759L, 1255L) */ ((var_1_11) > (10u))) {
		} else {
		}
	} else {
	}
	if (/* 522L, 142L, 150L, 836L, 865L, 1274L) */ ((var_1_12) != (/* 524L, 141L, 152L, 838L, 867L, 1276L) */ ((var_1_11) + (/* 526L, 140L, 154L, 840L, 869L, 1278L) */ ((var_1_11) * (10u))))))) {
	} else {
		if (/* 539L, 167L, 170L, 853L, 882L, 1291L) */ (! (var_1_22))) {
		} else {
		}
	}
	if (/* 551L, 194L, 202L, 928L, 945L, 1303L) */ ((/* 552L, 190L, 203L, 929L, 946L, 1304L) */ (max (/* 552L, 190L, 203L, 929L, 946L, 1304L) */ (var_1_18) , (var_1_19)))) != (/* 555L, 193L, 206L, 932L, 949L, 1307L) */ ((var_1_20) * (9999.5))))) {
	}
	if (/* 570L, 230L, 239L, 996L, 1012L, 1322L) */ ((/* 571L, 226L, 240L, 997L, 1013L, 1323L) */ ((var_1_7) / (/* 573L, 225L, 242L, 999L, 1015L, 1325L) */ (abs (var_1_23))))) > (/* 575L, 229L, 244L, 1001L, 1017L, 1327L) */ ((25) - (var_1_10))))) {
	}
	return /* 595L) */ ((
	/* 594L) */ ((
		/* 593L) */ ((
			/* 592L) */ ((
				/* 591L) */ ((
					/* 590L) */ ((
						/* 589L) */ ((
							/* 454L, 52L, 557L, 581L, 1206L) */ ((
								/* 455L, 7L, 14L, 558L, 582L, 1207L) */ ((
									/* 456L, 3L, 15L, 559L, 583L, 1208L) */ (! (
										var_1_2
									))
								) || (
									/* 458L, 6L, 17L, 561L, 585L, 1210L) */ ((
										var_1_3
									) && (
										var_1_4
									))
								))
							) ? (
								/* 461L, 46L, 564L, 588L, 1213L) */ ((
									/* 462L, 22L, 26L, 565L, 589L, 1214L) */ ((
										var_1_5
									) == (
										var_1_6
									))
								) ? (
									/* 465L, 32L, 568L, 592L, 1217L) */ ((
										var_1_1
									) == (
										/* 465L, 32L, 568L, 592L, 1217L) */ ((signed short int) (
											var_1_7
										))
									))
								) : (
									/* 469L, 44L, 572L, 596L, 1221L) */ ((
										var_1_1
									) == (
										/* 469L, 44L, 572L, 596L, 1221L) */ ((signed short int) (
											-128
										))
									))
								))
							) : (
								/* 473L, 50L, 576L, 600L, 1225L) */ ((
									var_1_1
								) == (
									/* 473L, 50L, 576L, 600L, 1225L) */ ((signed short int) (
										var_1_7
									))
								))
							))
						) && (
							/* 478L, 78L, 629L, 641L, 1230L) */ ((
								/* 479L, 61L, 67L, 630L, 642L, 1231L) */ ((
									var_1_7
								) > (
									/* 481L, 60L, 69L, 632L, 644L, 1233L) */ ((
										var_1_9
									) - (
										var_1_10
									))
								))
							) ? (
								/* 484L, 76L, 635L, 647L, 1236L) */ ((
									var_1_8
								) == (
									/* 484L, 76L, 635L, 647L, 1236L) */ ((signed long int) (
										/* 487L, 75L, 638L, 650L, 1239L) */ (abs (
											var_1_7
										))
									))
								))
							) : (
								1
							))
						))
					) && (
						/* 491L, 88L, 670L, 678L, 1243L) */ ((
							var_1_11
						) == (
							/* 491L, 88L, 670L, 678L, 1243L) */ ((unsigned long int) (
								/* 494L, 87L, 673L, 681L, 1246L) */ (min (
									/* 494L, 87L, 673L, 681L, 1246L) */ (
										var_1_10
									) , (
										var_1_12
									)
								))
							))
						))
					))
				) && (
					/* 498L, 130L, 731L, 754L, 1250L) */ ((
						/* 499L, 97L, 101L, 732L, 755L, 1251L) */ ((
							var_1_11
						) == (
							-50
						))
					) ? (
						/* 502L, 124L, 735L, 758L, 1254L) */ ((
							/* 503L, 106L, 110L, 736L, 759L, 1255L) */ ((
								var_1_11
							) > (
								10u
							))
						) ? (
							/* 506L, 118L, 739L, 762L, 1258L) */ ((
								var_1_13
							) == (
								/* 506L, 118L, 739L, 762L, 1258L) */ ((unsigned char) (
									/* 509L, 117L, 742L, 765L, 1261L) */ ((
										var_1_22
									) && (
										var_1_14
									))
								))
							))
						) : (
							/* 512L, 122L, 745L, 768L, 1264L) */ ((
								var_1_13
							) == (
								/* 512L, 122L, 745L, 768L, 1264L) */ ((unsigned char) (
									var_1_15
								))
							))
						))
					) : (
						/* 516L, 128L, 749L, 772L, 1268L) */ ((
							var_1_13
						) == (
							/* 516L, 128L, 749L, 772L, 1268L) */ ((unsigned char) (
								var_1_15
							))
						))
					))
				))
			) && (
				/* 521L, 183L, 835L, 864L, 1273L) */ ((
					/* 522L, 142L, 150L, 836L, 865L, 1274L) */ ((
						var_1_12
					) != (
						/* 524L, 141L, 152L, 838L, 867L, 1276L) */ ((
							var_1_11
						) + (
							/* 526L, 140L, 154L, 840L, 869L, 1278L) */ ((
								var_1_11
							) * (
								10u
							))
						))
					))
				) ? (
					/* 529L, 165L, 843L, 872L, 1281L) */ ((
						var_1_16
					) == (
						/* 529L, 165L, 843L, 872L, 1281L) */ ((unsigned char) (
							/* 532L, 164L, 846L, 875L, 1284L) */ ((
								/* 533L, 161L, 847L, 876L, 1285L) */ ((
									var_1_9
								) < (
									var_1_8
								))
							) && (
								/* 536L, 163L, 850L, 879L, 1288L) */ (! (
									var_1_15
								))
							))
						))
					))
				) : (
					/* 538L, 181L, 852L, 881L, 1290L) */ ((
						/* 539L, 167L, 170L, 853L, 882L, 1291L) */ (! (
							var_1_22
						))
					) ? (
						/* 541L, 175L, 855L, 884L, 1293L) */ ((
							var_1_16
						) == (
							/* 541L, 175L, 855L, 884L, 1293L) */ ((unsigned char) (
								0
							))
						))
					) : (
						/* 545L, 179L, 859L, 888L, 1297L) */ ((
							var_1_16
						) == (
							/* 545L, 179L, 859L, 888L, 1297L) */ ((unsigned char) (
								var_1_15
							))
						))
					))
				))
			))
		) && (
			/* 550L, 218L, 927L, 944L, 1302L) */ ((
				/* 551L, 194L, 202L, 928L, 945L, 1303L) */ ((
					/* 552L, 190L, 203L, 929L, 946L, 1304L) */ (max (
						/* 552L, 190L, 203L, 929L, 946L, 1304L) */ (
							var_1_18
						) , (
							var_1_19
						)
					))
				) != (
					/* 555L, 193L, 206L, 932L, 949L, 1307L) */ ((
						var_1_20
					) * (
						9999.5
					))
				))
			) ? (
				/* 558L, 216L, 935L, 952L, 1310L) */ ((
					var_1_17
				) == (
					/* 558L, 216L, 935L, 952L, 1310L) */ ((signed short int) (
						/* 561L, 215L, 938L, 955L, 1313L) */ ((
							/* 562L, 213L, 939L, 956L, 1314L) */ ((
								var_1_21
							) + (
								2
							))
						) + (
							-64
						))
					))
				))
			) : (
				1
			))
		))
	) && (
		/* 569L, 252L, 995L, 1011L, 1321L) */ ((
			/* 570L, 230L, 239L, 996L, 1012L, 1322L) */ ((
				/* 571L, 226L, 240L, 997L, 1013L, 1323L) */ ((
					var_1_7
				) / (
					/* 573L, 225L, 242L, 999L, 1015L, 1325L) */ (abs (
						var_1_23
					))
				))
			) > (
				/* 575L, 229L, 244L, 1001L, 1017L, 1327L) */ ((
					25
				) - (
					var_1_10
				))
			))
		) ? (
			/* 578L, 250L, 1004L, 1020L, 1330L) */ ((
				var_1_22
			) == (
				/* 578L, 250L, 1004L, 1020L, 1330L) */ ((unsigned char) (
					var_1_15
				))
			))
		) : (
			1
		))
	))
) && (
	/* 584L, 264L, 1038L, 1044L, 1336L) */ ((
		var_1_24
	) == (
		/* 584L, 264L, 1038L, 1044L, 1336L) */ ((signed char) (
			var_1_25
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
