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
void reach_error(void) { __assert_fail("0", "Req1_Prop1_Batch173Filler_PE_CI.c", 13, "reach_error"); }
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
float var_1_1 = 10000000.2;
float var_1_3 = 25.5;
float var_1_4 = 100000000000.75;
float var_1_5 = 1.25;
float var_1_6 = 128.75;
float var_1_7 = -0.25;
unsigned char var_1_8 = 1;
unsigned char var_1_9 = 1;
signed long int var_1_11 = -10;
unsigned char var_1_12 = 1;
unsigned char var_1_13 = 0;
unsigned char var_1_14 = 1;
unsigned long int var_1_15 = 4;
float var_1_16 = 10.2;
unsigned char var_1_17 = 100;
unsigned long int var_1_18 = 2895366789;
unsigned char var_1_19 = 128;
unsigned char var_1_20 = 1;
unsigned char var_1_21 = 0;
unsigned char var_1_22 = 1;
double var_1_23 = 99.8;
double var_1_24 = 1.8;
double var_1_25 = 4.75;
signed long int var_1_29 = -1;
unsigned long int var_1_30 = 256;
unsigned long int var_1_31 = 50;
unsigned long int var_1_32 = 8;
unsigned long int var_1_33 = 128;
unsigned long int var_1_34 = 5;
unsigned char var_1_35 = 0;
unsigned long int var_1_38 = 4;
unsigned char var_1_40 = 0;
unsigned char var_1_41 = 0;
float var_1_42 = 4.25;
unsigned long int var_1_43 = 4;
float var_1_44 = 2.8;
float var_1_45 = 2.5;
float var_1_46 = 9.75;
signed short int var_1_47 = 128;

// Calibration values

// Last'ed variables
unsigned char last_1_var_1_20 = 1;

// Additional functions


void initially(void) {
}



void step(void) {
	// From: Req5Batch173Filler_PE_CI
	/* 25L, 192L, 626L, 653L, 882L, 1007L) */ if (/* 5L, 158L, 159L, 627L, 654L, 862L, 1008L) */ ((/* 2L, 155L, 160L, 628L, 655L, 859L, 1009L) */ ((var_1_18) - (var_1_12))) >= (/* 4L, 157L, 163L, 631L, 658L, 861L, 1012L) */ (~ (var_1_14))))) {
		/* 20L, 186L, 633L, 660L, 877L, 1014L) */ if (last_1_var_1_20) {
			/* 15L, 181L, 635L, 662L, 872L, 1017L) */ var_1_17 = (
				/* 14L, 180L, 638L, 665L, 871L, 1020L) */ (max (
					/* 14L, 180L, 638L, 665L, 871L, 1020L) */ (
						/* 12L, 178L, 639L, 666L, 869L, 1021L) */ ((
							var_1_19
						) - (
							var_1_14
						))
					) , (
						var_1_12
					)
				))
			);
		} else {
			/* 19L, 185L, 643L, 670L, 876L, 1025L) */ var_1_17 = (
				var_1_12
			);
		}
	} else {
		/* 24L, 191L, 647L, 674L, 881L, 1029L) */ var_1_17 = (
			var_1_14
		);
	}


	// From: Req6Batch173Filler_PE_CI
	unsigned char stepLocal_2 = var_1_13;
	unsigned char stepLocal_1 = /* 1035L, 204L, 208L, 735L, 766L) */ ((/* 1036L, 202L, 209L, 736L, 767L) */ (max (/* 1036L, 202L, 209L, 736L, 767L) */ (var_1_4) , (var_1_3)))) >= (var_1_5));
	/* 1067L, 265L, 733L, 764L) */ if (/* 1045L, 206L, 207L, 734L, 765L) */ ((stepLocal_1) || (var_1_9))) {
		/* 1062L, 259L, 741L, 772L) */ if (/* 1047L, 223L, 224L, 742L, 773L) */ ((var_1_17) > (stepLocal_2))) {
			/* 1057L, 253L, 745L, 776L) */ if (var_1_9) {
				/* 1052L, 236L, 747L, 778L) */ var_1_20 = (
					var_1_21
				);
			} else {
				/* 1056L, 252L, 751L, 782L) */ var_1_20 = (
					0
				);
			}
		} else {
			/* 1061L, 258L, 755L, 786L) */ var_1_20 = (
				0
			);
		}
	} else {
		/* 1066L, 264L, 759L, 790L) */ var_1_20 = (
			var_1_22
		);
	}


	// From: Req3Batch173Filler_PE_CI
	/* 964L, 111L, 451L, 481L) */ if (/* 965L, 78L, 79L, 452L, 482L) */ ((var_1_13) > (2))) {
		/* 968L, 103L, 455L, 485L) */ if (var_1_20) {
			/* 970L, 96L, 457L, 487L) */ var_1_15 = (
				/* 973L, 95L, 460L, 490L) */ (max (
					/* 973L, 95L, 460L, 490L) */ (
						/* 974L, 91L, 461L, 491L) */ (abs (
							var_1_13
						))
					) , (
						/* 976L, 94L, 463L, 493L) */ ((
							2813524572u
						) - (
							var_1_17
						))
					)
				))
			);
		} else {
			/* 979L, 102L, 466L, 496L) */ var_1_15 = (
				/* 982L, 101L, 469L, 499L) */ (min (
					/* 982L, 101L, 469L, 499L) */ (
						var_1_17
					) , (
						var_1_14
					)
				))
			);
		}
	} else {
		/* 985L, 110L, 472L, 502L) */ var_1_15 = (
			/* 988L, 109L, 475L, 505L) */ ((
				var_1_17
			) + (
				100u
			))
		);
	}


	// From: Req4Batch173Filler_PE_CI
	/* 993L, 145L, 570L, 584L) */ if (/* 994L, 123L, 124L, 571L, 585L) */ ((var_1_11) <= (-128))) {
		/* 997L, 143L, 574L, 588L) */ if (/* 998L, 132L, 133L, 575L, 589L) */ ((var_1_6) <= (var_1_7))) {
			/* 1001L, 142L, 578L, 592L) */ var_1_16 = (
				var_1_5
			);
		}
	}


	// From: Req1Batch173Filler_PE_CI
	/* 913L, 28L, 269L, 289L) */ if (/* 914L, 5L, 6L, 270L, 290L) */ (! (/* 915L, 4L, 7L, 271L, 291L) */ ((100u) >= (var_1_15))))) {
		/* 918L, 19L, 274L, 294L) */ var_1_1 = (
			/* 921L, 18L, 277L, 297L) */ (max (
				/* 921L, 18L, 277L, 297L) */ (
					var_1_3
				) , (
					var_1_4
				)
			))
		);
	} else {
		/* 924L, 27L, 280L, 300L) */ var_1_1 = (
			/* 927L, 26L, 283L, 303L) */ ((
				/* 928L, 24L, 284L, 304L) */ ((
					var_1_5
				) - (
					var_1_6
				))
			) + (
				var_1_7
			))
		);
	}


	// From: Req2Batch173Filler_PE_CI
	unsigned long int stepLocal_0 = var_1_15;
	/* 958L, 70L, 349L, 374L) */ if (var_1_20) {
		/* 953L, 64L, 351L, 376L) */ if (/* 940L, 41L, 42L, 352L, 377L) */ ((/* 939L, 39L, 43L, 353L, 378L) */ ((var_1_15) / (var_1_11))) != (stepLocal_0))) {
			/* 948L, 59L, 357L, 382L) */ var_1_8 = (
				/* 947L, 58L, 360L, 385L) */ ((
					/* 945L, 56L, 361L, 386L) */ ((
						var_1_12
					) + (
						var_1_13
					))
				) + (
					var_1_14
				))
			);
		} else {
			/* 952L, 63L, 365L, 390L) */ var_1_8 = (
				var_1_14
			);
		}
	} else {
		/* 957L, 69L, 369L, 394L) */ var_1_8 = (
			var_1_12
		);
	}


	// From: CodeObject1
	/* 298L, 61L) */ var_1_23 = (
		var_1_24
	);


	// From: CodeObject2
	/* 303L, 91L) */ if (/* 304L, 72L, 73L) */ ((/* 305L, 70L, 74L) */ ((/* 306L, 68L, 75L) */ ((25) * (var_1_17))) ^ (var_1_17))) > (var_1_11))) {
		/* 311L, 90L) */ var_1_25 = (
			var_1_24
		);
	}


	// From: CodeObject3
	/* 315L, 112L) */ if (/* 316L, 99L, 100L) */ ((var_1_24) > (var_1_23))) {
		/* 319L, 111L) */ var_1_29 = (
			/* 322L, 110L) */ (abs (
				/* 323L, 109L) */ (abs (
					var_1_15
				))
			))
		);
	}


	// From: CodeObject4
	/* 326L, 141L) */ if (/* 327L, 119L, 120L) */ ((var_1_24) < (/* 329L, 118L, 122L) */ (abs (var_1_25))))) {
		/* 331L, 140L) */ var_1_30 = (
			/* 334L, 139L) */ ((
				/* 335L, 133L) */ ((
					/* 336L, 131L) */ (abs (
						var_1_31
					))
				) + (
					256u
				))
			) + (
				/* 339L, 138L) */ (min (
					/* 339L, 138L) */ (
						/* 340L, 136L) */ (max (
							/* 340L, 136L) */ (
								var_1_32
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


	// From: CodeObject5
	/* 367L, 185L) */ if (/* 368L, 154L, 155L) */ ((/* 369L, 152L, 156L) */ ((/* 370L, 149L, 157L) */ (max (/* 370L, 149L, 157L) */ (var_1_14) , (var_1_13)))) >> (/* 373L, 151L, 160L) */ (abs (var_1_38))))) > (var_1_32))) {
		/* 376L, 178L) */ var_1_35 = (
			/* 379L, 177L) */ ((
				/* 380L, 175L) */ ((
					var_1_20
				) && (
					var_1_40
				))
			) || (
				var_1_41
			))
		);
	} else {
		/* 384L, 184L) */ var_1_35 = (
			/* 387L, 183L) */ ((
				var_1_41
			) || (
				var_1_40
			))
		);
	}


	// From: CodeObject6
	/* 446L, 239L) */ if (/* 447L, 194L, 195L) */ ((/* 448L, 192L, 196L) */ (max (/* 448L, 192L, 196L) */ (var_1_34) , (/* 450L, 191L, 198L) */ (abs (var_1_13)))))) == (32u))) {
		/* 453L, 210L) */ var_1_42 = (
			var_1_24
		);
	} else {
		/* 457L, 237L) */ if (/* 458L, 219L, 220L) */ ((var_1_15) < (/* 460L, 218L, 222L) */ (~ (var_1_43))))) {
			/* 462L, 236L) */ var_1_42 = (
				/* 465L, 235L) */ (abs (
					/* 466L, 234L) */ ((
						/* 467L, 232L) */ ((
							var_1_44
						) + (
							var_1_45
						))
					) - (
						var_1_46
					))
				))
			);
		}
	}


	// From: CodeObject7
	/* 472L, 293L) */ if (/* 473L, 253L, 254L) */ ((/* 474L, 249L, 255L) */ ((var_1_19) - (var_1_13))) > (/* 477L, 252L, 258L) */ (min (/* 477L, 252L, 258L) */ (var_1_15) , (var_1_13)))))) {
		/* 480L, 291L) */ if (/* 481L, 270L, 271L) */ ((var_1_13) >= (5))) {
			/* 484L, 286L) */ var_1_47 = (
				var_1_13
			);
		} else {
			/* 488L, 290L) */ var_1_47 = (
				var_1_14
			);
		}
	}
}



void updateVariables(void) {
	var_1_3 = __VERIFIER_nondet_float();
	assume_abort_if_not((var_1_3 >= -922337.2036854766000e+13F && var_1_3 <= -1.0e-20F) || (var_1_3 <= 9223372.036854766000e+12F && var_1_3 >= 1.0e-20F ));
	var_1_4 = __VERIFIER_nondet_float();
	assume_abort_if_not((var_1_4 >= -922337.2036854766000e+13F && var_1_4 <= -1.0e-20F) || (var_1_4 <= 9223372.036854766000e+12F && var_1_4 >= 1.0e-20F ));
	var_1_5 = __VERIFIER_nondet_float();
	assume_abort_if_not((var_1_5 >= 0.0F && var_1_5 <= -1.0e-20F) || (var_1_5 <= 4611686.018427383000e+12F && var_1_5 >= 1.0e-20F ));
	var_1_6 = __VERIFIER_nondet_float();
	assume_abort_if_not((var_1_6 >= 0.0F && var_1_6 <= -1.0e-20F) || (var_1_6 <= 4611686.018427383000e+12F && var_1_6 >= 1.0e-20F ));
	var_1_7 = __VERIFIER_nondet_float();
	assume_abort_if_not((var_1_7 >= -461168.6018427383000e+13F && var_1_7 <= -1.0e-20F) || (var_1_7 <= 4611686.018427383000e+12F && var_1_7 >= 1.0e-20F ));
	var_1_9 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_9 >= 0);
	assume_abort_if_not(var_1_9 <= 1);
	var_1_11 = __VERIFIER_nondet_long();
	assume_abort_if_not(var_1_11 >= -2147483648);
	assume_abort_if_not(var_1_11 <= 2147483647);
	assume_abort_if_not(var_1_11 != 0);
	var_1_12 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_12 >= 0);
	assume_abort_if_not(var_1_12 <= 64);
	var_1_13 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_13 >= 0);
	assume_abort_if_not(var_1_13 <= 63);
	var_1_14 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_14 >= 0);
	assume_abort_if_not(var_1_14 <= 127);
	var_1_18 = __VERIFIER_nondet_ulong();
	assume_abort_if_not(var_1_18 >= 2147483647);
	assume_abort_if_not(var_1_18 <= 4294967295);
	var_1_19 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_19 >= 127);
	assume_abort_if_not(var_1_19 <= 254);
	var_1_21 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_21 >= 0);
	assume_abort_if_not(var_1_21 <= 0);
	var_1_22 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_22 >= 1);
	assume_abort_if_not(var_1_22 <= 1);
	var_1_24 = __VERIFIER_nondet_double();
	assume_abort_if_not((var_1_24 >= -922337.2036854766000e+13F && var_1_24 <= -1.0e-20F) || (var_1_24 <= 9223372.036854766000e+12F && var_1_24 >= 1.0e-20F ));
	var_1_31 = __VERIFIER_nondet_ulong();
	assume_abort_if_not(var_1_31 >= 0);
	assume_abort_if_not(var_1_31 <= 1073741824);
	var_1_32 = __VERIFIER_nondet_ulong();
	assume_abort_if_not(var_1_32 >= 0);
	assume_abort_if_not(var_1_32 <= 2147483647);
	var_1_33 = __VERIFIER_nondet_ulong();
	assume_abort_if_not(var_1_33 >= 0);
	assume_abort_if_not(var_1_33 <= 2147483647);
	var_1_34 = __VERIFIER_nondet_ulong();
	assume_abort_if_not(var_1_34 >= 0);
	assume_abort_if_not(var_1_34 <= 2147483647);
	var_1_38 = __VERIFIER_nondet_ulong();
	assume_abort_if_not(var_1_38 >= 1);
	assume_abort_if_not(var_1_38 <= 30);
	var_1_40 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_40 >= 0);
	assume_abort_if_not(var_1_40 <= 0);
	var_1_41 = __VERIFIER_nondet_uchar();
	assume_abort_if_not(var_1_41 >= 0);
	assume_abort_if_not(var_1_41 <= 0);
	var_1_43 = __VERIFIER_nondet_ulong();
	assume_abort_if_not(var_1_43 >= 1);
	assume_abort_if_not(var_1_43 <= 6);
	var_1_44 = __VERIFIER_nondet_float();
	assume_abort_if_not((var_1_44 >= 0.0F && var_1_44 <= -1.0e-20F) || (var_1_44 <= 4611686.018427383000e+12F && var_1_44 >= 1.0e-20F ));
	var_1_45 = __VERIFIER_nondet_float();
	assume_abort_if_not((var_1_45 >= 0.0F && var_1_45 <= -1.0e-20F) || (var_1_45 <= 4611686.018427383000e+12F && var_1_45 >= 1.0e-20F ));
	var_1_46 = __VERIFIER_nondet_float();
	assume_abort_if_not((var_1_46 >= 0.0F && var_1_46 <= -1.0e-20F) || (var_1_46 <= 9223372.036854766000e+12F && var_1_46 >= 1.0e-20F ));
}



void updateLastVariables(void) {
	last_1_var_1_20 = var_1_20;
}

int property(void) {
	if (/* 493L, 5L, 10L, 310L, 330L, 1073L) */ (! (/* 494L, 4L, 11L, 311L, 331L, 1074L) */ ((100u) >= (var_1_15))))) {
	} else {
	}
	if (var_1_20) {
		if (/* 515L, 41L, 47L, 402L, 427L, 1095L) */ ((/* 516L, 39L, 48L, 403L, 428L, 1096L) */ ((var_1_15) / (var_1_11))) != (var_1_15))) {
		} else {
		}
	} else {
	}
	if (/* 540L, 78L, 82L, 512L, 542L, 1120L) */ ((var_1_13) > (2))) {
		if (var_1_20) {
		} else {
		}
	} else {
	}
	if (/* 569L, 123L, 127L, 599L, 613L, 1149L) */ ((var_1_11) <= (-128))) {
		if (/* 573L, 132L, 136L, 603L, 617L, 1153L) */ ((var_1_6) <= (var_1_7))) {
		}
	}
	if (/* 583L, 158L, 165L, 681L, 708L, 890L, 1163L, 33L) */ ((/* 584L, 155L, 166L, 682L, 709L, 887L, 1164L, 30L) */ ((var_1_18) - (var_1_12))) >= (/* 587L, 157L, 169L, 685L, 712L, 889L, 1167L, 32L) */ (~ (var_1_14))))) {
		if (last_1_var_1_20) {
		} else {
		}
	} else {
	}
	if (/* 610L, 206L, 214L, 796L, 827L, 1190L) */ ((/* 611L, 204L, 215L, 797L, 828L, 1191L) */ ((/* 612L, 202L, 216L, 798L, 829L, 1192L) */ (max (/* 612L, 202L, 216L, 798L, 829L, 1192L) */ (var_1_4) , (var_1_3)))) >= (var_1_5))) || (var_1_9))) {
		if (/* 618L, 223L, 227L, 804L, 835L, 1198L) */ ((var_1_17) > (var_1_13))) {
			if (var_1_9) {
			} else {
			}
		} else {
		}
	} else {
	}
	return /* 644L) */ ((
	/* 643L) */ ((
		/* 642L) */ ((
			/* 641L) */ ((
				/* 640L) */ ((
					/* 492L, 29L, 309L, 329L, 1072L) */ ((
						/* 493L, 5L, 10L, 310L, 330L, 1073L) */ (! (
							/* 494L, 4L, 11L, 311L, 331L, 1074L) */ ((
								100u
							) >= (
								var_1_15
							))
						))
					) ? (
						/* 497L, 19L, 314L, 334L, 1077L) */ ((
							var_1_1
						) == (
							/* 497L, 19L, 314L, 334L, 1077L) */ ((float) (
								/* 500L, 18L, 317L, 337L, 1080L) */ (max (
									/* 500L, 18L, 317L, 337L, 1080L) */ (
										var_1_3
									) , (
										var_1_4
									)
								))
							))
						))
					) : (
						/* 503L, 27L, 320L, 340L, 1083L) */ ((
							var_1_1
						) == (
							/* 503L, 27L, 320L, 340L, 1083L) */ ((float) (
								/* 506L, 26L, 323L, 343L, 1086L) */ ((
									/* 507L, 24L, 324L, 344L, 1087L) */ ((
										var_1_5
									) - (
										var_1_6
									))
								) + (
									var_1_7
								))
							))
						))
					))
				) && (
					/* 512L, 71L, 399L, 424L, 1092L) */ ((
						var_1_20
					) ? (
						/* 514L, 65L, 401L, 426L, 1094L) */ ((
							/* 515L, 41L, 47L, 402L, 427L, 1095L) */ ((
								/* 516L, 39L, 48L, 403L, 428L, 1096L) */ ((
									var_1_15
								) / (
									var_1_11
								))
							) != (
								var_1_15
							))
						) ? (
							/* 520L, 59L, 407L, 432L, 1100L) */ ((
								var_1_8
							) == (
								/* 520L, 59L, 407L, 432L, 1100L) */ ((unsigned char) (
									/* 523L, 58L, 410L, 435L, 1103L) */ ((
										/* 524L, 56L, 411L, 436L, 1104L) */ ((
											var_1_12
										) + (
											var_1_13
										))
									) + (
										var_1_14
									))
								))
							))
						) : (
							/* 528L, 63L, 415L, 440L, 1108L) */ ((
								var_1_8
							) == (
								/* 528L, 63L, 415L, 440L, 1108L) */ ((unsigned char) (
									var_1_14
								))
							))
						))
					) : (
						/* 532L, 69L, 419L, 444L, 1112L) */ ((
							var_1_8
						) == (
							/* 532L, 69L, 419L, 444L, 1112L) */ ((unsigned char) (
								var_1_12
							))
						))
					))
				))
			) && (
				/* 539L, 112L, 511L, 541L, 1119L) */ ((
					/* 540L, 78L, 82L, 512L, 542L, 1120L) */ ((
						var_1_13
					) > (
						2
					))
				) ? (
					/* 543L, 104L, 515L, 545L, 1123L) */ ((
						var_1_20
					) ? (
						/* 545L, 96L, 517L, 547L, 1125L) */ ((
							var_1_15
						) == (
							/* 545L, 96L, 517L, 547L, 1125L) */ ((unsigned long int) (
								/* 548L, 95L, 520L, 550L, 1128L) */ (max (
									/* 548L, 95L, 520L, 550L, 1128L) */ (
										/* 549L, 91L, 521L, 551L, 1129L) */ (abs (
											var_1_13
										))
									) , (
										/* 551L, 94L, 523L, 553L, 1131L) */ ((
											2813524572u
										) - (
											var_1_17
										))
									)
								))
							))
						))
					) : (
						/* 554L, 102L, 526L, 556L, 1134L) */ ((
							var_1_15
						) == (
							/* 554L, 102L, 526L, 556L, 1134L) */ ((unsigned long int) (
								/* 557L, 101L, 529L, 559L, 1137L) */ (min (
									/* 557L, 101L, 529L, 559L, 1137L) */ (
										var_1_17
									) , (
										var_1_14
									)
								))
							))
						))
					))
				) : (
					/* 560L, 110L, 532L, 562L, 1140L) */ ((
						var_1_15
					) == (
						/* 560L, 110L, 532L, 562L, 1140L) */ ((unsigned long int) (
							/* 563L, 109L, 535L, 565L, 1143L) */ ((
								var_1_17
							) + (
								100u
							))
						))
					))
				))
			))
		) && (
			/* 568L, 146L, 598L, 612L, 1148L) */ ((
				/* 569L, 123L, 127L, 599L, 613L, 1149L) */ ((
					var_1_11
				) <= (
					-128
				))
			) ? (
				/* 572L, 144L, 602L, 616L, 1152L) */ ((
					/* 573L, 132L, 136L, 603L, 617L, 1153L) */ ((
						var_1_6
					) <= (
						var_1_7
					))
				) ? (
					/* 576L, 142L, 606L, 620L, 1156L) */ ((
						var_1_16
					) == (
						/* 576L, 142L, 606L, 620L, 1156L) */ ((float) (
							var_1_5
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
		/* 582L, 193L, 680L, 707L, 910L, 1162L, 53L) */ ((
			/* 583L, 158L, 165L, 681L, 708L, 890L, 1163L, 33L) */ ((
				/* 584L, 155L, 166L, 682L, 709L, 887L, 1164L, 30L) */ ((
					var_1_18
				) - (
					var_1_12
				))
			) >= (
				/* 587L, 157L, 169L, 685L, 712L, 889L, 1167L, 32L) */ (~ (
					var_1_14
				))
			))
		) ? (
			/* 589L, 187L, 687L, 714L, 905L, 1169L, 48L) */ ((
				last_1_var_1_20
			) ? (
				/* 592L, 181L, 689L, 716L, 900L, 1172L, 43L) */ ((
					var_1_17
				) == (
					/* 592L, 181L, 689L, 716L, 900L, 1172L, 43L) */ ((unsigned char) (
						/* 595L, 180L, 692L, 719L, 899L, 1175L, 42L) */ (max (
							/* 595L, 180L, 692L, 719L, 899L, 1175L, 42L) */ (
								/* 596L, 178L, 693L, 720L, 897L, 1176L, 40L) */ ((
									var_1_19
								) - (
									var_1_14
								))
							) , (
								var_1_12
							)
						))
					))
				))
			) : (
				/* 600L, 185L, 697L, 724L, 904L, 1180L, 47L) */ ((
					var_1_17
				) == (
					/* 600L, 185L, 697L, 724L, 904L, 1180L, 47L) */ ((unsigned char) (
						var_1_12
					))
				))
			))
		) : (
			/* 604L, 191L, 701L, 728L, 909L, 1184L, 52L) */ ((
				var_1_17
			) == (
				/* 604L, 191L, 701L, 728L, 909L, 1184L, 52L) */ ((unsigned char) (
					var_1_14
				))
			))
		))
	))
) && (
	/* 609L, 266L, 795L, 826L, 1189L) */ ((
		/* 610L, 206L, 214L, 796L, 827L, 1190L) */ ((
			/* 611L, 204L, 215L, 797L, 828L, 1191L) */ ((
				/* 612L, 202L, 216L, 798L, 829L, 1192L) */ (max (
					/* 612L, 202L, 216L, 798L, 829L, 1192L) */ (
						var_1_4
					) , (
						var_1_3
					)
				))
			) >= (
				var_1_5
			))
		) || (
			var_1_9
		))
	) ? (
		/* 617L, 260L, 803L, 834L, 1197L) */ ((
			/* 618L, 223L, 227L, 804L, 835L, 1198L) */ ((
				var_1_17
			) > (
				var_1_13
			))
		) ? (
			/* 621L, 254L, 807L, 838L, 1201L) */ ((
				var_1_9
			) ? (
				/* 623L, 236L, 809L, 840L, 1203L) */ ((
					var_1_20
				) == (
					/* 623L, 236L, 809L, 840L, 1203L) */ ((unsigned char) (
						var_1_21
					))
				))
			) : (
				/* 627L, 252L, 813L, 844L, 1207L) */ ((
					var_1_20
				) == (
					/* 627L, 252L, 813L, 844L, 1207L) */ ((unsigned char) (
						0
					))
				))
			))
		) : (
			/* 631L, 258L, 817L, 848L, 1211L) */ ((
				var_1_20
			) == (
				/* 631L, 258L, 817L, 848L, 1211L) */ ((unsigned char) (
					0
				))
			))
		))
	) : (
		/* 635L, 264L, 821L, 852L, 1215L) */ ((
			var_1_20
		) == (
			/* 635L, 264L, 821L, 852L, 1215L) */ ((unsigned char) (
				var_1_22
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
