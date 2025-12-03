// This file is part of the SV-Benchmarks collection of verification tasks:
// https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks
//
// SPDX-FileCopyrightText: 2025 Jana Berger
//
// SPDX-License-Identifier: GPL-3.0-or-later

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
void reach_error(void) { __assert_fail("0", "Req1_Prop1_Batch79Amount500.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
void initially(void);
void step(void);
void updateVariables(void);
void updateLastVariables(void);
int property(void);
int main(void);
unsigned char isInitial = 0;
signed short int var_1_1 = 0;
signed short int var_1_5 = -32;
signed short int var_1_6 = 256;
signed short int var_1_7 = 8;
signed short int var_1_8 = 10;
signed short int var_1_9 = -4;
signed short int var_1_10 = -16;
signed short int var_1_11 = 4;
unsigned short int var_1_12 = 4;
signed short int var_1_13 = 64;
signed short int var_1_15 = -5;
signed short int var_1_16 = 31520;
signed short int var_1_17 = 2;
signed short int var_1_18 = 25;
signed short int var_1_19 = 25;
signed long int var_1_20 = -2;
unsigned long int var_1_22 = 8;
unsigned long int var_1_23 = 2088673933;
unsigned long int var_1_24 = 0;
signed long int var_1_25 = -16;
signed long int var_1_26 = 128;
unsigned short int var_1_27 = 50010;
double var_1_28 = 49.4;
double var_1_30 = 63.5;
double var_1_31 = 49.25;
double var_1_32 = 3.25;
double var_1_33 = 99.6;
double var_1_34 = 64.4;
signed char var_1_35 = -64;
signed char var_1_36 = 0;
signed char var_1_37 = 2;
signed char var_1_38 = 1;
double var_1_39 = 31.6;
double var_1_40 = 4.55;
double var_1_41 = 10.75;
float var_1_42 = 25.25;
float var_1_43 = 1.5;
signed char var_1_44 = -100;
signed char var_1_45 = 32;
signed char var_1_46 = 2;
signed short int var_1_47 = -100;
unsigned char var_1_48 = 64;
unsigned long int var_1_49 = 256;
unsigned long int var_1_50 = 32;
unsigned long int var_1_51 = 8;
unsigned long int var_1_52 = 2802607859;
signed char var_1_53 = 0;
signed char var_1_54 = 10;
signed long int var_1_55 = 128;
double var_1_56 = 16.5;
signed char var_1_58 = 4;
signed long int var_1_59 = 8;
signed long int var_1_60 = 1845177938;
signed long int var_1_61 = 2027085789;
signed long int var_1_62 = 1625620335;
signed long int var_1_63 = 2134167206;
unsigned short int var_1_66 = 4;
unsigned short int var_1_67 = 19397;
unsigned long int var_1_68 = 25;
unsigned short int var_1_69 = 128;
unsigned short int var_1_70 = 53169;
unsigned short int var_1_71 = 25122;
unsigned long int var_1_72 = 5;
unsigned short int var_1_73 = 59269;
unsigned char var_1_74 = 64;
unsigned char var_1_75 = 8;
unsigned short int var_1_76 = 4;
signed short int var_1_77 = 8;
signed char var_1_78 = 2;
unsigned char var_1_79 = 0;
unsigned char var_1_80 = 0;
unsigned char var_1_81 = 0;
unsigned char var_1_82 = 1;
unsigned char var_1_83 = 0;
unsigned char var_1_84 = 0;
signed char var_1_85 = -1;
signed char var_1_86 = -10;
signed char var_1_87 = 100;
signed char var_1_88 = -50;
unsigned long int var_1_89 = 128;
unsigned char var_1_90 = 2;
signed short int var_1_91 = -2;
signed long int var_1_92 = -50;
unsigned char var_1_93 = 10;
double var_1_94 = 16.5;
unsigned long int var_1_95 = 0;
unsigned char var_1_96 = 0;
unsigned short int var_1_97 = 50;
float var_1_98 = 16.5;
signed long int var_1_99 = 100000000;
unsigned long int var_1_100 = 5;
signed long int var_1_101 = 4;
double var_1_102 = 64.2;
unsigned char var_1_103 = 0;
unsigned long int var_1_104 = 128;
unsigned short int var_1_105 = 32;
signed long int last_1_var_1_26 = 128;
unsigned long int last_1_var_1_95 = 0;
unsigned char last_1_var_1_96 = 0;
signed long int last_1_var_1_101 = 4;
unsigned char last_1_var_1_103 = 0;
unsigned short int last_1_var_1_105 = 32;
void initially(void) {
}
void step(void) {
 if (last_1_var_1_96) {
  var_1_24 = ((((var_1_12) > (var_1_16)) ? (var_1_12) : (var_1_16)));
 } else {
  if (var_1_7 >= (last_1_var_1_26 * last_1_var_1_105)) {
   var_1_24 = ((((var_1_16) < 0 ) ? -(var_1_16) : (var_1_16)));
  } else {
   var_1_24 = (((((((var_1_18) < (var_1_19)) ? (var_1_18) : (var_1_19))) < 0 ) ? -((((var_1_18) < (var_1_19)) ? (var_1_18) : (var_1_19))) : ((((var_1_18) < (var_1_19)) ? (var_1_18) : (var_1_19)))));
  }
 }
 unsigned char stepLocal_7 = last_1_var_1_103;
 signed long int stepLocal_6 = (((var_1_16) > (var_1_17)) ? (var_1_16) : (var_1_17));
 signed long int stepLocal_5 = var_1_9 * var_1_6;
 signed long int stepLocal_4 = last_1_var_1_101;
 if (var_1_9 > stepLocal_6) {
  if (var_1_5 >= stepLocal_4) {
   if (last_1_var_1_95 <= stepLocal_5) {
    if (last_1_var_1_103) {
     var_1_22 = (2999457086u - var_1_16);
    }
   } else {
    var_1_22 = ((((var_1_13) > (var_1_16)) ? (var_1_13) : (var_1_16)));
   }
  } else {
   if (stepLocal_7 || (var_1_13 <= var_1_19)) {
    var_1_22 = ((((((var_1_23 - var_1_12)) > (var_1_18)) ? ((var_1_23 - var_1_12)) : (var_1_18))) + var_1_13);
   }
  }
 } else {
  var_1_22 = (3017035728u - 100u);
 }
 var_1_48 = (((((var_1_45) > (var_1_38)) ? (var_1_45) : (var_1_38))) + ((((var_1_46) < 0 ) ? -(var_1_46) : (var_1_46))));
 unsigned long int stepLocal_17 = var_1_24;
 if ((var_1_7 + var_1_19) != stepLocal_17) {
  var_1_49 = (var_1_23 + var_1_45);
 } else {
  if ((var_1_40 - var_1_41) < var_1_30) {
   var_1_49 = ((var_1_23 - var_1_18) + ((((var_1_19) > (var_1_7)) ? (var_1_19) : (var_1_7))));
  } else {
   var_1_49 = (((((var_1_18) < (((((var_1_16) > (var_1_13)) ? (var_1_16) : (var_1_13))))) ? (var_1_18) : (((((var_1_16) > (var_1_13)) ? (var_1_16) : (var_1_13)))))) + (((((var_1_27 + var_1_38)) > (var_1_12)) ? ((var_1_27 + var_1_38)) : (var_1_12))));
  }
 }
 signed short int stepLocal_36 = var_1_19;
 if (stepLocal_36 > (var_1_22 / var_1_72)) {
  var_1_88 = ((((var_1_45 + var_1_72) < 0 ) ? -(var_1_45 + var_1_72) : (var_1_45 + var_1_72)));
 } else {
  var_1_88 = ((((var_1_46) < (var_1_12)) ? (var_1_46) : (var_1_12)));
 }
 var_1_89 = ((((var_1_7) < (100000000u)) ? (var_1_7) : (100000000u)));
 signed char stepLocal_37 = var_1_87;
 if (var_1_12 <= stepLocal_37) {
  var_1_90 = var_1_37;
 }
 var_1_91 = var_1_10;
 var_1_93 = var_1_75;
 var_1_94 = var_1_41;
 var_1_95 = 2u;
 var_1_96 = var_1_81;
 var_1_97 = var_1_46;
 if (var_1_96) {
  var_1_98 = var_1_32;
 }
 var_1_99 = -16;
 if (var_1_96) {
  var_1_100 = 256u;
 }
 if (var_1_80) {
  var_1_102 = 10.125;
 } else {
  var_1_102 = var_1_41;
 }
 if (var_1_81) {
  var_1_103 = 1;
 }
 if (var_1_96) {
  var_1_104 = var_1_52;
 }
 if (var_1_96) {
  var_1_25 = var_1_15;
 } else {
  var_1_25 = (((((var_1_19 - var_1_13) + (var_1_12 - var_1_16)) < 0 ) ? -((var_1_19 - var_1_13) + (var_1_12 - var_1_16)) : ((var_1_19 - var_1_13) + (var_1_12 - var_1_16))));
 }
 signed short int stepLocal_11 = var_1_5;
 signed short int stepLocal_10 = var_1_16;
 unsigned short int stepLocal_9 = var_1_12;
 signed long int stepLocal_8 = var_1_6 - var_1_16;
 if (var_1_16 <= stepLocal_11) {
  if (stepLocal_9 != (((((var_1_27 - var_1_18)) > (var_1_17)) ? ((var_1_27 - var_1_18)) : (var_1_17)))) {
   if (var_1_18 <= stepLocal_10) {
    if (var_1_19 >= stepLocal_8) {
     var_1_26 = (var_1_13 + (var_1_17 - var_1_7));
    } else {
     if (var_1_103) {
      var_1_26 = -4;
     }
    }
   }
  } else {
   var_1_26 = (((((var_1_16) < ((128 + var_1_19))) ? (var_1_16) : ((128 + var_1_19)))) - var_1_7);
  }
 }
 if (var_1_103) {
  var_1_34 = var_1_31;
 } else {
  var_1_34 = ((((var_1_31) > (var_1_33)) ? (var_1_31) : (var_1_33)));
 }
 if (var_1_103) {
  if ((var_1_95 / (64 + var_1_45)) <= var_1_97) {
   var_1_50 = (var_1_51 + (((((var_1_23 - var_1_7)) < ((var_1_27 + var_1_13))) ? ((var_1_23 - var_1_7)) : ((var_1_27 + var_1_13)))));
  }
 } else {
  if (var_1_32 >= ((var_1_40 - var_1_31) * var_1_34)) {
   var_1_50 = (var_1_52 - var_1_17);
  }
 }
 signed long int stepLocal_21 = (50 >> 10u) * var_1_45;
 signed char stepLocal_20 = var_1_37;
 if (stepLocal_20 <= ((var_1_36 | var_1_45) * var_1_97)) {
  if (stepLocal_21 >= var_1_100) {
   var_1_58 = ((((var_1_36) < (var_1_46)) ? (var_1_36) : (var_1_46)));
  } else {
   var_1_58 = (((((var_1_54 + var_1_45)) < (var_1_37)) ? ((var_1_54 + var_1_45)) : (var_1_37)));
  }
 } else {
  var_1_58 = var_1_12;
 }
 unsigned long int stepLocal_23 = var_1_95;
 unsigned long int stepLocal_22 = var_1_23 + var_1_46;
 if ((var_1_40 - var_1_41) <= var_1_43) {
  if (stepLocal_22 > var_1_37) {
   var_1_59 = ((((((var_1_60) > (var_1_61)) ? (var_1_60) : (var_1_61))) - var_1_18) - (((((var_1_62 - var_1_95)) < ((var_1_63 - var_1_7))) ? ((var_1_62 - var_1_95)) : ((var_1_63 - var_1_7)))));
  }
 } else {
  if (stepLocal_23 != var_1_104) {
   var_1_59 = ((((var_1_10) > (-128)) ? (var_1_10) : (-128)));
  }
 }
 if (var_1_102 <= (- (var_1_31 - var_1_33))) {
  if ((- var_1_41) >= var_1_31) {
   var_1_66 = ((((((var_1_16 - var_1_13)) < ((var_1_67 - 1))) ? ((var_1_16 - var_1_13)) : ((var_1_67 - 1)))) + ((((var_1_19) > (var_1_45)) ? (var_1_19) : (var_1_45))));
  }
 }
 if ((-128 >= var_1_9) && var_1_96) {
  var_1_68 = (var_1_7 + var_1_67);
 } else {
  var_1_68 = (var_1_52 - var_1_89);
 }
 unsigned long int stepLocal_29 = var_1_22;
 unsigned long int stepLocal_28 = var_1_72;
 unsigned long int stepLocal_27 = var_1_49;
 if (stepLocal_27 > (var_1_22 / var_1_70)) {
  var_1_74 = ((((var_1_46) > (var_1_72)) ? (var_1_46) : (var_1_72)));
 } else {
  if (var_1_22 > stepLocal_28) {
   var_1_74 = var_1_38;
  } else {
   if (var_1_103) {
    var_1_74 = (((((var_1_72) > (var_1_46)) ? (var_1_72) : (var_1_46))) + var_1_38);
   } else {
    if (stepLocal_29 <= 16u) {
     var_1_74 = (var_1_38 + var_1_72);
    } else {
     var_1_74 = ((((var_1_72) > (var_1_75)) ? (var_1_72) : (var_1_75)));
    }
   }
  }
 }
 if (var_1_103) {
  if (var_1_96) {
   var_1_78 = var_1_37;
  }
 } else {
  var_1_78 = (var_1_12 - var_1_38);
 }
 if (var_1_103) {
  var_1_85 = ((((var_1_46) < (((((var_1_54) < 0 ) ? -(var_1_54) : (var_1_54))))) ? (var_1_46) : (((((var_1_54) < 0 ) ? -(var_1_54) : (var_1_54))))));
 } else {
  if (var_1_8 > ((((var_1_10) > (var_1_68)) ? (var_1_10) : (var_1_68)))) {
   var_1_85 = (-16 + var_1_12);
  } else {
   var_1_85 = ((((((((var_1_72) > (var_1_12)) ? (var_1_72) : (var_1_12)))) < (var_1_45)) ? (((((var_1_72) > (var_1_12)) ? (var_1_72) : (var_1_12)))) : (var_1_45)));
  }
 }
 if (var_1_103) {
  var_1_92 = var_1_54;
 } else {
  var_1_92 = var_1_68;
 }
 signed long int stepLocal_39 = -5;
 unsigned long int stepLocal_38 = var_1_52 - (var_1_70 + var_1_66);
 if (var_1_54 < stepLocal_39) {
  if (var_1_24 < stepLocal_38) {
   var_1_105 = ((((var_1_71) < 0 ) ? -(var_1_71) : (var_1_71)));
  }
 }
 signed long int stepLocal_33 = var_1_60 + 16;
 unsigned long int stepLocal_32 = (var_1_26 * var_1_99) + var_1_72;
 unsigned short int stepLocal_31 = var_1_71;
 unsigned long int stepLocal_30 = 128u * var_1_61;
 if (var_1_41 < 0.19999999999999996) {
  if (var_1_22 >= stepLocal_30) {
   var_1_79 = (! (! var_1_80));
  } else {
   if (var_1_105 < stepLocal_32) {
    var_1_79 = (var_1_81 && var_1_82);
   } else {
    if (var_1_80) {
     var_1_79 = ((63.8 <= var_1_33) || var_1_81);
    }
   }
  }
 } else {
  if (var_1_68 >= stepLocal_33) {
   var_1_79 = (var_1_81 || var_1_82);
  } else {
   if (stepLocal_31 >= var_1_22) {
    var_1_79 = ((var_1_81 && var_1_83) || var_1_84);
   }
  }
 }
 if (var_1_79) {
  var_1_101 = 0;
 }
 if (var_1_96 && var_1_79) {
  if (var_1_102 != 16.5) {
   var_1_1 = ((((-256) > (var_1_5)) ? (-256) : (var_1_5)));
  } else {
   var_1_1 = (var_1_6 - var_1_7);
  }
 } else {
  var_1_1 = (((((var_1_8) < (var_1_9)) ? (var_1_8) : (var_1_9))) + var_1_10);
 }
 signed long int stepLocal_3 = (((32) > (var_1_9)) ? (32) : (var_1_9));
 signed long int stepLocal_2 = ~ (var_1_8 ^ var_1_9);
 signed long int stepLocal_1 = (var_1_5 + var_1_9) << ((((var_1_12) < 0 ) ? -(var_1_12) : (var_1_12)));
 unsigned long int stepLocal_0 = var_1_68 | (var_1_6 % var_1_15);
 if (stepLocal_1 <= (var_1_8 * var_1_7)) {
  var_1_11 = ((var_1_12 + var_1_13) - var_1_7);
 } else {
  if (stepLocal_2 <= ((var_1_10 * var_1_7) & ((((-50) > (var_1_13)) ? (-50) : (var_1_13))))) {
   if (var_1_79) {
    if (stepLocal_0 >= var_1_8) {
     var_1_11 = (var_1_12 - (var_1_16 - var_1_13));
    }
   } else {
    var_1_11 = (var_1_9 + var_1_10);
   }
  } else {
   if (stepLocal_3 != (var_1_12 & (var_1_16 - var_1_13))) {
    var_1_11 = (((var_1_12 - var_1_17) + (var_1_18 - var_1_19)) + -100);
   } else {
    var_1_11 = var_1_9;
   }
  }
 }
 if ((var_1_7 ^ (~ var_1_16)) > var_1_13) {
  if (var_1_26 >= var_1_11) {
   var_1_20 = (((((var_1_13 - var_1_18) < 0 ) ? -(var_1_13 - var_1_18) : (var_1_13 - var_1_18))) - var_1_16);
  }
 } else {
  var_1_20 = ((((var_1_6) < 0 ) ? -(var_1_6) : (var_1_6)));
 }
 unsigned long int stepLocal_13 = - (3611439333u - var_1_13);
 unsigned long int stepLocal_12 = var_1_100;
 if (stepLocal_12 >= var_1_8) {
  var_1_35 = ((((var_1_12) > (var_1_36)) ? (var_1_12) : (var_1_36)));
 } else {
  if ((8 | var_1_50) > stepLocal_13) {
   var_1_35 = (var_1_12 - ((((var_1_37) > (var_1_38)) ? (var_1_37) : (var_1_38))));
  } else {
   var_1_35 = (var_1_12 + -25);
  }
 }
 unsigned long int stepLocal_16 = ~ var_1_22;
 unsigned char stepLocal_15 = var_1_96;
 unsigned long int stepLocal_14 = (((var_1_16) > (var_1_23)) ? (var_1_16) : (var_1_23));
 if (var_1_7 <= stepLocal_14) {
  if (var_1_9 <= stepLocal_16) {
   if (stepLocal_15 && var_1_79) {
    var_1_42 = ((((var_1_40) < 0 ) ? -(var_1_40) : (var_1_40)));
   }
  } else {
   var_1_42 = (var_1_41 - (var_1_40 + ((((var_1_43) < 0 ) ? -(var_1_43) : (var_1_43)))));
  }
 } else {
  var_1_42 = ((((8.75f) < 0 ) ? -(8.75f) : (8.75f)));
 }
 if ((var_1_23 + (var_1_10 * var_1_92)) != var_1_7) {
  var_1_44 = (var_1_37 - ((var_1_45 - var_1_12) + var_1_46));
 } else {
  var_1_44 = (var_1_46 - var_1_37);
 }
 if (var_1_23 > var_1_100) {
  var_1_47 = (((((var_1_12 + var_1_10) < 0 ) ? -(var_1_12 + var_1_10) : (var_1_12 + var_1_10))) - var_1_46);
 } else {
  if (var_1_79) {
   var_1_47 = ((var_1_16 - ((((var_1_45) < (var_1_12)) ? (var_1_45) : (var_1_12)))) - ((var_1_19 + var_1_18) + var_1_46));
  } else {
   var_1_47 = (((1 + 8) + ((((var_1_104) > (var_1_38)) ? (var_1_104) : (var_1_38)))) + (var_1_12 + var_1_46));
  }
 }
 unsigned char stepLocal_18 = var_1_26 > var_1_38;
 if (var_1_79 && stepLocal_18) {
  var_1_53 = (((((var_1_45 + (var_1_12 + var_1_54))) < (var_1_36)) ? ((var_1_45 + (var_1_12 + var_1_54))) : (var_1_36)));
 } else {
  if (127.4f < var_1_31) {
   var_1_53 = (((((var_1_46) < ((var_1_54 + var_1_12))) ? (var_1_46) : ((var_1_54 + var_1_12)))) + var_1_45);
  } else {
   var_1_53 = ((((var_1_37) > ((var_1_54 + var_1_46))) ? (var_1_37) : ((var_1_54 + var_1_46))));
  }
 }
 unsigned long int stepLocal_19 = (var_1_49 | var_1_25) & (var_1_46 | var_1_23);
 if (var_1_41 <= (var_1_94 / ((((var_1_56) < 0 ) ? -(var_1_56) : (var_1_56))))) {
  if ((var_1_59 / (var_1_27 - var_1_45)) != stepLocal_19) {
   var_1_55 = (var_1_38 - (var_1_45 + var_1_16));
  } else {
   var_1_55 = ((((((((var_1_9) < (var_1_92)) ? (var_1_9) : (var_1_92)))) < (var_1_105)) ? (((((var_1_9) < (var_1_92)) ? (var_1_9) : (var_1_92)))) : (var_1_105)));
  }
 }
 signed long int stepLocal_26 = var_1_16 * (128 * var_1_6);
 signed short int stepLocal_25 = var_1_13;
 unsigned long int stepLocal_24 = var_1_89 >> ((((var_1_72) < 0 ) ? -(var_1_72) : (var_1_72)));
 if (! var_1_79) {
  if (stepLocal_25 == var_1_15) {
   if (var_1_68 < stepLocal_26) {
    var_1_69 = (var_1_70 - var_1_16);
   } else {
    var_1_69 = ((var_1_16 + var_1_71) - var_1_12);
   }
  } else {
   if (((((var_1_24) < (var_1_27)) ? (var_1_24) : (var_1_27))) <= stepLocal_24) {
    var_1_69 = ((((((var_1_73 - var_1_89)) > (var_1_70)) ? ((var_1_73 - var_1_89)) : (var_1_70))) - (((((var_1_72) > (var_1_45)) ? (var_1_72) : (var_1_45))) + ((((var_1_12) < 0 ) ? -(var_1_12) : (var_1_12)))));
   } else {
    var_1_69 = var_1_45;
   }
  }
 } else {
  var_1_69 = ((((((var_1_71 - var_1_18) + ((((var_1_19) < (var_1_89)) ? (var_1_19) : (var_1_89))))) > (var_1_12)) ? (((var_1_71 - var_1_18) + ((((var_1_19) < (var_1_89)) ? (var_1_19) : (var_1_89))))) : (var_1_12)));
 }
 if ((- var_1_70) > ((((var_1_5) < 0 ) ? -(var_1_5) : (var_1_5)))) {
  if (((var_1_67 << var_1_27) >= ((((var_1_73) < (var_1_92)) ? (var_1_73) : (var_1_92)))) && var_1_103) {
   var_1_76 = (var_1_70 - 10);
  } else {
   var_1_76 = ((var_1_73 - var_1_90) - ((((var_1_46) < 0 ) ? -(var_1_46) : (var_1_46))));
  }
 } else {
  var_1_76 = (var_1_37 + var_1_12);
 }
 if (var_1_79) {
  var_1_77 = ((((var_1_45) < (((((var_1_92) < 0 ) ? -(var_1_92) : (var_1_92))))) ? (var_1_45) : (((((var_1_92) < 0 ) ? -(var_1_92) : (var_1_92))))));
 } else {
  var_1_77 = ((((((var_1_19 + var_1_17) - 16)) < (var_1_46)) ? (((var_1_19 + var_1_17) - 16)) : (var_1_46)));
 }
 signed long int stepLocal_35 = var_1_92 / var_1_15;
 unsigned long int stepLocal_34 = var_1_51;
 if (var_1_24 >= stepLocal_34) {
  var_1_86 = (var_1_12 - var_1_46);
 } else {
  if (var_1_25 > stepLocal_35) {
   var_1_86 = (1 - 100);
  } else {
   var_1_86 = (var_1_45 - (var_1_87 - var_1_12));
  }
 }
 if (0 < var_1_55) {
  if (! (var_1_22 >= var_1_13)) {
   if (var_1_79) {
    var_1_28 = ((((var_1_30) > (-0.5)) ? (var_1_30) : (-0.5)));
   } else {
    var_1_28 = (var_1_31 - ((((var_1_32 - var_1_33) < 0 ) ? -(var_1_32 - var_1_33) : (var_1_32 - var_1_33))));
   }
  } else {
   var_1_28 = ((((var_1_32) < (var_1_30)) ? (var_1_32) : (var_1_30)));
  }
 }
 if (var_1_28 < var_1_30) {
  var_1_39 = (((((var_1_33 - (var_1_40 + var_1_41))) < (var_1_30)) ? ((var_1_33 - (var_1_40 + var_1_41))) : (var_1_30)));
 }
}
void updateVariables(void) {
 var_1_5 = __VERIFIER_nondet_short();
 assume_abort_if_not(var_1_5 >= -32767);
 assume_abort_if_not(var_1_5 <= 32766);
 var_1_6 = __VERIFIER_nondet_short();
 assume_abort_if_not(var_1_6 >= -1);
 assume_abort_if_not(var_1_6 <= 32766);
 var_1_7 = __VERIFIER_nondet_short();
 assume_abort_if_not(var_1_7 >= 0);
 assume_abort_if_not(var_1_7 <= 32766);
 var_1_8 = __VERIFIER_nondet_short();
 assume_abort_if_not(var_1_8 >= -16383);
 assume_abort_if_not(var_1_8 <= 16383);
 var_1_9 = __VERIFIER_nondet_short();
 assume_abort_if_not(var_1_9 >= -16383);
 assume_abort_if_not(var_1_9 <= 16383);
 var_1_10 = __VERIFIER_nondet_short();
 assume_abort_if_not(var_1_10 >= -16383);
 assume_abort_if_not(var_1_10 <= 16383);
 var_1_12 = __VERIFIER_nondet_ushort();
 assume_abort_if_not(var_1_12 >= 0);
 assume_abort_if_not(var_1_12 <= 14);
 var_1_13 = __VERIFIER_nondet_short();
 assume_abort_if_not(var_1_13 >= 0);
 assume_abort_if_not(var_1_13 <= 16383);
 var_1_15 = __VERIFIER_nondet_short();
 assume_abort_if_not(var_1_15 >= -32768);
 assume_abort_if_not(var_1_15 <= 32767);
 assume_abort_if_not(var_1_15 != 0);
 var_1_16 = __VERIFIER_nondet_short();
 assume_abort_if_not(var_1_16 >= 16383);
 assume_abort_if_not(var_1_16 <= 32766);
 var_1_17 = __VERIFIER_nondet_short();
 assume_abort_if_not(var_1_17 >= 0);
 assume_abort_if_not(var_1_17 <= 8191);
 var_1_18 = __VERIFIER_nondet_short();
 assume_abort_if_not(var_1_18 >= 0);
 assume_abort_if_not(var_1_18 <= 8191);
 var_1_19 = __VERIFIER_nondet_short();
 assume_abort_if_not(var_1_19 >= 0);
 assume_abort_if_not(var_1_19 <= 8191);
 var_1_23 = __VERIFIER_nondet_ulong();
 assume_abort_if_not(var_1_23 >= 1073741823);
 assume_abort_if_not(var_1_23 <= 2147483647);
 var_1_27 = __VERIFIER_nondet_ushort();
 assume_abort_if_not(var_1_27 >= 32767);
 assume_abort_if_not(var_1_27 <= 65535);
 var_1_30 = __VERIFIER_nondet_double();
 assume_abort_if_not((var_1_30 >= -922337.2036854766000e+13F && var_1_30 <= -1.0e-20F) || (var_1_30 <= 9223372.036854766000e+12F && var_1_30 >= 1.0e-20F ));
 var_1_31 = __VERIFIER_nondet_double();
 assume_abort_if_not((var_1_31 >= 0.0F && var_1_31 <= -1.0e-20F) || (var_1_31 <= 9223372.036854766000e+12F && var_1_31 >= 1.0e-20F ));
 var_1_32 = __VERIFIER_nondet_double();
 assume_abort_if_not((var_1_32 >= 0.0F && var_1_32 <= -1.0e-20F) || (var_1_32 <= 9223372.036854766000e+12F && var_1_32 >= 1.0e-20F ));
 var_1_33 = __VERIFIER_nondet_double();
 assume_abort_if_not((var_1_33 >= 0.0F && var_1_33 <= -1.0e-20F) || (var_1_33 <= 9223372.036854766000e+12F && var_1_33 >= 1.0e-20F ));
 var_1_36 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_36 >= -127);
 assume_abort_if_not(var_1_36 <= 126);
 var_1_37 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_37 >= 0);
 assume_abort_if_not(var_1_37 <= 126);
 var_1_38 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_38 >= 0);
 assume_abort_if_not(var_1_38 <= 126);
 var_1_40 = __VERIFIER_nondet_double();
 assume_abort_if_not((var_1_40 >= 0.0F && var_1_40 <= -1.0e-20F) || (var_1_40 <= 4611686.018427383000e+12F && var_1_40 >= 1.0e-20F ));
 var_1_41 = __VERIFIER_nondet_double();
 assume_abort_if_not((var_1_41 >= 0.0F && var_1_41 <= -1.0e-20F) || (var_1_41 <= 4611686.018427383000e+12F && var_1_41 >= 1.0e-20F ));
 var_1_43 = __VERIFIER_nondet_float();
 assume_abort_if_not((var_1_43 >= -461168.6018427383000e+13F && var_1_43 <= -1.0e-20F) || (var_1_43 <= 4611686.018427383000e+12F && var_1_43 >= 1.0e-20F ));
 var_1_45 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_45 >= 31);
 assume_abort_if_not(var_1_45 <= 63);
 var_1_46 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_46 >= 0);
 assume_abort_if_not(var_1_46 <= 63);
 var_1_51 = __VERIFIER_nondet_ulong();
 assume_abort_if_not(var_1_51 >= 0);
 assume_abort_if_not(var_1_51 <= 2147483647);
 var_1_52 = __VERIFIER_nondet_ulong();
 assume_abort_if_not(var_1_52 >= 2147483647);
 assume_abort_if_not(var_1_52 <= 4294967294);
 var_1_54 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_54 >= -31);
 assume_abort_if_not(var_1_54 <= 31);
 var_1_56 = __VERIFIER_nondet_double();
 assume_abort_if_not((var_1_56 >= -922337.2036854776000e+13F && var_1_56 <= -1.0e-20F) || (var_1_56 <= 9223372.036854776000e+12F && var_1_56 >= 1.0e-20F ));
 assume_abort_if_not(var_1_56 != 0.0F);
 var_1_60 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_60 >= 1073741822);
 assume_abort_if_not(var_1_60 <= 2147483646);
 var_1_61 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_61 >= 1073741822);
 assume_abort_if_not(var_1_61 <= 2147483646);
 var_1_62 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_62 >= 1073741823);
 assume_abort_if_not(var_1_62 <= 2147483646);
 var_1_63 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_63 >= 1073741823);
 assume_abort_if_not(var_1_63 <= 2147483646);
 var_1_67 = __VERIFIER_nondet_ushort();
 assume_abort_if_not(var_1_67 >= 16383);
 assume_abort_if_not(var_1_67 <= 32767);
 var_1_70 = __VERIFIER_nondet_ushort();
 assume_abort_if_not(var_1_70 >= 32767);
 assume_abort_if_not(var_1_70 <= 65534);
 var_1_71 = __VERIFIER_nondet_ushort();
 assume_abort_if_not(var_1_71 >= 16384);
 assume_abort_if_not(var_1_71 <= 32767);
 var_1_72 = __VERIFIER_nondet_ulong();
 assume_abort_if_not(var_1_72 >= 1);
 assume_abort_if_not(var_1_72 <= 7);
 var_1_73 = __VERIFIER_nondet_ushort();
 assume_abort_if_not(var_1_73 >= 49150);
 assume_abort_if_not(var_1_73 <= 65534);
 var_1_75 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_75 >= 0);
 assume_abort_if_not(var_1_75 <= 254);
 var_1_80 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_80 >= 0);
 assume_abort_if_not(var_1_80 <= 0);
 var_1_81 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_81 >= 1);
 assume_abort_if_not(var_1_81 <= 1);
 var_1_82 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_82 >= 1);
 assume_abort_if_not(var_1_82 <= 1);
 var_1_83 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_83 >= 0);
 assume_abort_if_not(var_1_83 <= 0);
 var_1_84 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_84 >= 0);
 assume_abort_if_not(var_1_84 <= 0);
 var_1_87 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_87 >= 63);
 assume_abort_if_not(var_1_87 <= 126);
}
void updateLastVariables(void) {
 last_1_var_1_26 = var_1_26;
 last_1_var_1_95 = var_1_95;
 last_1_var_1_96 = var_1_96;
 last_1_var_1_101 = var_1_101;
 last_1_var_1_103 = var_1_103;
 last_1_var_1_105 = var_1_105;
}
int property(void) {
 return (((((((((((((((((((((((((((((((((((((((((((((((((var_1_96 && var_1_79) ? ((var_1_102 != 16.5) ? (var_1_1 == ((signed short int) ((((-256) > (var_1_5)) ? (-256) : (var_1_5))))) : (var_1_1 == ((signed short int) (var_1_6 - var_1_7)))) : (var_1_1 == ((signed short int) (((((var_1_8) < (var_1_9)) ? (var_1_8) : (var_1_9))) + var_1_10)))) && ((((var_1_5 + var_1_9) << ((((var_1_12) < 0 ) ? -(var_1_12) : (var_1_12)))) <= (var_1_8 * var_1_7)) ? (var_1_11 == ((signed short int) ((var_1_12 + var_1_13) - var_1_7))) : (((~ (var_1_8 ^ var_1_9)) <= ((var_1_10 * var_1_7) & ((((-50) > (var_1_13)) ? (-50) : (var_1_13))))) ? (var_1_79 ? (((var_1_68 | (var_1_6 % var_1_15)) >= var_1_8) ? (var_1_11 == ((signed short int) (var_1_12 - (var_1_16 - var_1_13)))) : 1) : (var_1_11 == ((signed short int) (var_1_9 + var_1_10)))) : ((((((32) > (var_1_9)) ? (32) : (var_1_9))) != (var_1_12 & (var_1_16 - var_1_13))) ? (var_1_11 == ((signed short int) (((var_1_12 - var_1_17) + (var_1_18 - var_1_19)) + -100))) : (var_1_11 == ((signed short int) var_1_9)))))) && (((var_1_7 ^ (~ var_1_16)) > var_1_13) ? ((var_1_26 >= var_1_11) ? (var_1_20 == ((signed long int) (((((var_1_13 - var_1_18) < 0 ) ? -(var_1_13 - var_1_18) : (var_1_13 - var_1_18))) - var_1_16))) : 1) : (var_1_20 == ((signed long int) ((((var_1_6) < 0 ) ? -(var_1_6) : (var_1_6))))))) && ((var_1_9 > ((((var_1_16) > (var_1_17)) ? (var_1_16) : (var_1_17)))) ? ((var_1_5 >= last_1_var_1_101) ? ((last_1_var_1_95 <= (var_1_9 * var_1_6)) ? (last_1_var_1_103 ? (var_1_22 == ((unsigned long int) (2999457086u - var_1_16))) : 1) : (var_1_22 == ((unsigned long int) ((((var_1_13) > (var_1_16)) ? (var_1_13) : (var_1_16)))))) : ((last_1_var_1_103 || (var_1_13 <= var_1_19)) ? (var_1_22 == ((unsigned long int) ((((((var_1_23 - var_1_12)) > (var_1_18)) ? ((var_1_23 - var_1_12)) : (var_1_18))) + var_1_13))) : 1)) : (var_1_22 == ((unsigned long int) (3017035728u - 100u))))) && (last_1_var_1_96 ? (var_1_24 == ((unsigned long int) ((((var_1_12) > (var_1_16)) ? (var_1_12) : (var_1_16))))) : ((var_1_7 >= (last_1_var_1_26 * last_1_var_1_105)) ? (var_1_24 == ((unsigned long int) ((((var_1_16) < 0 ) ? -(var_1_16) : (var_1_16))))) : (var_1_24 == ((unsigned long int) (((((((var_1_18) < (var_1_19)) ? (var_1_18) : (var_1_19))) < 0 ) ? -((((var_1_18) < (var_1_19)) ? (var_1_18) : (var_1_19))) : ((((var_1_18) < (var_1_19)) ? (var_1_18) : (var_1_19)))))))))) && (var_1_96 ? (var_1_25 == ((signed long int) var_1_15)) : (var_1_25 == ((signed long int) (((((var_1_19 - var_1_13) + (var_1_12 - var_1_16)) < 0 ) ? -((var_1_19 - var_1_13) + (var_1_12 - var_1_16)) : ((var_1_19 - var_1_13) + (var_1_12 - var_1_16)))))))) && ((var_1_16 <= var_1_5) ? ((var_1_12 != (((((var_1_27 - var_1_18)) > (var_1_17)) ? ((var_1_27 - var_1_18)) : (var_1_17)))) ? ((var_1_18 <= var_1_16) ? ((var_1_19 >= (var_1_6 - var_1_16)) ? (var_1_26 == ((signed long int) (var_1_13 + (var_1_17 - var_1_7)))) : (var_1_103 ? (var_1_26 == ((signed long int) -4)) : 1)) : 1) : (var_1_26 == ((signed long int) (((((var_1_16) < ((128 + var_1_19))) ? (var_1_16) : ((128 + var_1_19)))) - var_1_7)))) : 1)) && ((0 < var_1_55) ? ((! (var_1_22 >= var_1_13)) ? (var_1_79 ? (var_1_28 == ((double) ((((var_1_30) > (-0.5)) ? (var_1_30) : (-0.5))))) : (var_1_28 == ((double) (var_1_31 - ((((var_1_32 - var_1_33) < 0 ) ? -(var_1_32 - var_1_33) : (var_1_32 - var_1_33))))))) : (var_1_28 == ((double) ((((var_1_32) < (var_1_30)) ? (var_1_32) : (var_1_30)))))) : 1)) && (var_1_103 ? (var_1_34 == ((double) var_1_31)) : (var_1_34 == ((double) ((((var_1_31) > (var_1_33)) ? (var_1_31) : (var_1_33))))))) && ((var_1_100 >= var_1_8) ? (var_1_35 == ((signed char) ((((var_1_12) > (var_1_36)) ? (var_1_12) : (var_1_36))))) : (((8 | var_1_50) > (- (3611439333u - var_1_13))) ? (var_1_35 == ((signed char) (var_1_12 - ((((var_1_37) > (var_1_38)) ? (var_1_37) : (var_1_38)))))) : (var_1_35 == ((signed char) (var_1_12 + -25)))))) && ((var_1_28 < var_1_30) ? (var_1_39 == ((double) (((((var_1_33 - (var_1_40 + var_1_41))) < (var_1_30)) ? ((var_1_33 - (var_1_40 + var_1_41))) : (var_1_30))))) : 1)) && ((var_1_7 <= ((((var_1_16) > (var_1_23)) ? (var_1_16) : (var_1_23)))) ? ((var_1_9 <= (~ var_1_22)) ? ((var_1_96 && var_1_79) ? (var_1_42 == ((float) ((((var_1_40) < 0 ) ? -(var_1_40) : (var_1_40))))) : 1) : (var_1_42 == ((float) (var_1_41 - (var_1_40 + ((((var_1_43) < 0 ) ? -(var_1_43) : (var_1_43)))))))) : (var_1_42 == ((float) ((((8.75f) < 0 ) ? -(8.75f) : (8.75f))))))) && (((var_1_23 + (var_1_10 * var_1_92)) != var_1_7) ? (var_1_44 == ((signed char) (var_1_37 - ((var_1_45 - var_1_12) + var_1_46)))) : (var_1_44 == ((signed char) (var_1_46 - var_1_37))))) && ((var_1_23 > var_1_100) ? (var_1_47 == ((signed short int) (((((var_1_12 + var_1_10) < 0 ) ? -(var_1_12 + var_1_10) : (var_1_12 + var_1_10))) - var_1_46))) : (var_1_79 ? (var_1_47 == ((signed short int) ((var_1_16 - ((((var_1_45) < (var_1_12)) ? (var_1_45) : (var_1_12)))) - ((var_1_19 + var_1_18) + var_1_46)))) : (var_1_47 == ((signed short int) (((1 + 8) + ((((var_1_104) > (var_1_38)) ? (var_1_104) : (var_1_38)))) + (var_1_12 + var_1_46))))))) && (var_1_48 == ((unsigned char) (((((var_1_45) > (var_1_38)) ? (var_1_45) : (var_1_38))) + ((((var_1_46) < 0 ) ? -(var_1_46) : (var_1_46))))))) && (((var_1_7 + var_1_19) != var_1_24) ? (var_1_49 == ((unsigned long int) (var_1_23 + var_1_45))) : (((var_1_40 - var_1_41) < var_1_30) ? (var_1_49 == ((unsigned long int) ((var_1_23 - var_1_18) + ((((var_1_19) > (var_1_7)) ? (var_1_19) : (var_1_7)))))) : (var_1_49 == ((unsigned long int) (((((var_1_18) < (((((var_1_16) > (var_1_13)) ? (var_1_16) : (var_1_13))))) ? (var_1_18) : (((((var_1_16) > (var_1_13)) ? (var_1_16) : (var_1_13)))))) + (((((var_1_27 + var_1_38)) > (var_1_12)) ? ((var_1_27 + var_1_38)) : (var_1_12))))))))) && (var_1_103 ? (((var_1_95 / (64 + var_1_45)) <= var_1_97) ? (var_1_50 == ((unsigned long int) (var_1_51 + (((((var_1_23 - var_1_7)) < ((var_1_27 + var_1_13))) ? ((var_1_23 - var_1_7)) : ((var_1_27 + var_1_13))))))) : 1) : ((var_1_32 >= ((var_1_40 - var_1_31) * var_1_34)) ? (var_1_50 == ((unsigned long int) (var_1_52 - var_1_17))) : 1))) && ((var_1_79 && (var_1_26 > var_1_38)) ? (var_1_53 == ((signed char) (((((var_1_45 + (var_1_12 + var_1_54))) < (var_1_36)) ? ((var_1_45 + (var_1_12 + var_1_54))) : (var_1_36))))) : ((127.4f < var_1_31) ? (var_1_53 == ((signed char) (((((var_1_46) < ((var_1_54 + var_1_12))) ? (var_1_46) : ((var_1_54 + var_1_12)))) + var_1_45))) : (var_1_53 == ((signed char) ((((var_1_37) > ((var_1_54 + var_1_46))) ? (var_1_37) : ((var_1_54 + var_1_46))))))))) && ((var_1_41 <= (var_1_94 / ((((var_1_56) < 0 ) ? -(var_1_56) : (var_1_56))))) ? (((var_1_59 / (var_1_27 - var_1_45)) != ((var_1_49 | var_1_25) & (var_1_46 | var_1_23))) ? (var_1_55 == ((signed long int) (var_1_38 - (var_1_45 + var_1_16)))) : (var_1_55 == ((signed long int) ((((((((var_1_9) < (var_1_92)) ? (var_1_9) : (var_1_92)))) < (var_1_105)) ? (((((var_1_9) < (var_1_92)) ? (var_1_9) : (var_1_92)))) : (var_1_105)))))) : 1)) && ((var_1_37 <= ((var_1_36 | var_1_45) * var_1_97)) ? ((((50 >> 10u) * var_1_45) >= var_1_100) ? (var_1_58 == ((signed char) ((((var_1_36) < (var_1_46)) ? (var_1_36) : (var_1_46))))) : (var_1_58 == ((signed char) (((((var_1_54 + var_1_45)) < (var_1_37)) ? ((var_1_54 + var_1_45)) : (var_1_37)))))) : (var_1_58 == ((signed char) var_1_12)))) && (((var_1_40 - var_1_41) <= var_1_43) ? (((var_1_23 + var_1_46) > var_1_37) ? (var_1_59 == ((signed long int) ((((((var_1_60) > (var_1_61)) ? (var_1_60) : (var_1_61))) - var_1_18) - (((((var_1_62 - var_1_95)) < ((var_1_63 - var_1_7))) ? ((var_1_62 - var_1_95)) : ((var_1_63 - var_1_7))))))) : 1) : ((var_1_95 != var_1_104) ? (var_1_59 == ((signed long int) ((((var_1_10) > (-128)) ? (var_1_10) : (-128))))) : 1))) && ((var_1_102 <= (- (var_1_31 - var_1_33))) ? (((- var_1_41) >= var_1_31) ? (var_1_66 == ((unsigned short int) ((((((var_1_16 - var_1_13)) < ((var_1_67 - 1))) ? ((var_1_16 - var_1_13)) : ((var_1_67 - 1)))) + ((((var_1_19) > (var_1_45)) ? (var_1_19) : (var_1_45)))))) : 1) : 1)) && (((-128 >= var_1_9) && var_1_96) ? (var_1_68 == ((unsigned long int) (var_1_7 + var_1_67))) : (var_1_68 == ((unsigned long int) (var_1_52 - var_1_89))))) && ((! var_1_79) ? ((var_1_13 == var_1_15) ? ((var_1_68 < (var_1_16 * (128 * var_1_6))) ? (var_1_69 == ((unsigned short int) (var_1_70 - var_1_16))) : (var_1_69 == ((unsigned short int) ((var_1_16 + var_1_71) - var_1_12)))) : ((((((var_1_24) < (var_1_27)) ? (var_1_24) : (var_1_27))) <= (var_1_89 >> ((((var_1_72) < 0 ) ? -(var_1_72) : (var_1_72))))) ? (var_1_69 == ((unsigned short int) ((((((var_1_73 - var_1_89)) > (var_1_70)) ? ((var_1_73 - var_1_89)) : (var_1_70))) - (((((var_1_72) > (var_1_45)) ? (var_1_72) : (var_1_45))) + ((((var_1_12) < 0 ) ? -(var_1_12) : (var_1_12))))))) : (var_1_69 == ((unsigned short int) var_1_45)))) : (var_1_69 == ((unsigned short int) ((((((var_1_71 - var_1_18) + ((((var_1_19) < (var_1_89)) ? (var_1_19) : (var_1_89))))) > (var_1_12)) ? (((var_1_71 - var_1_18) + ((((var_1_19) < (var_1_89)) ? (var_1_19) : (var_1_89))))) : (var_1_12))))))) && ((var_1_49 > (var_1_22 / var_1_70)) ? (var_1_74 == ((unsigned char) ((((var_1_46) > (var_1_72)) ? (var_1_46) : (var_1_72))))) : ((var_1_22 > var_1_72) ? (var_1_74 == ((unsigned char) var_1_38)) : (var_1_103 ? (var_1_74 == ((unsigned char) (((((var_1_72) > (var_1_46)) ? (var_1_72) : (var_1_46))) + var_1_38))) : ((var_1_22 <= 16u) ? (var_1_74 == ((unsigned char) (var_1_38 + var_1_72))) : (var_1_74 == ((unsigned char) ((((var_1_72) > (var_1_75)) ? (var_1_72) : (var_1_75)))))))))) && (((- var_1_70) > ((((var_1_5) < 0 ) ? -(var_1_5) : (var_1_5)))) ? ((((var_1_67 << var_1_27) >= ((((var_1_73) < (var_1_92)) ? (var_1_73) : (var_1_92)))) && var_1_103) ? (var_1_76 == ((unsigned short int) (var_1_70 - 10))) : (var_1_76 == ((unsigned short int) ((var_1_73 - var_1_90) - ((((var_1_46) < 0 ) ? -(var_1_46) : (var_1_46))))))) : (var_1_76 == ((unsigned short int) (var_1_37 + var_1_12))))) && (var_1_79 ? (var_1_77 == ((signed short int) ((((var_1_45) < (((((var_1_92) < 0 ) ? -(var_1_92) : (var_1_92))))) ? (var_1_45) : (((((var_1_92) < 0 ) ? -(var_1_92) : (var_1_92)))))))) : (var_1_77 == ((signed short int) ((((((var_1_19 + var_1_17) - 16)) < (var_1_46)) ? (((var_1_19 + var_1_17) - 16)) : (var_1_46))))))) && (var_1_103 ? (var_1_96 ? (var_1_78 == ((signed char) var_1_37)) : 1) : (var_1_78 == ((signed char) (var_1_12 - var_1_38))))) && ((var_1_41 < 0.19999999999999996) ? ((var_1_22 >= (128u * var_1_61)) ? (var_1_79 == ((unsigned char) (! (! var_1_80)))) : ((var_1_105 < ((var_1_26 * var_1_99) + var_1_72)) ? (var_1_79 == ((unsigned char) (var_1_81 && var_1_82))) : (var_1_80 ? (var_1_79 == ((unsigned char) ((63.8 <= var_1_33) || var_1_81))) : 1))) : ((var_1_68 >= (var_1_60 + 16)) ? (var_1_79 == ((unsigned char) (var_1_81 || var_1_82))) : ((var_1_71 >= var_1_22) ? (var_1_79 == ((unsigned char) ((var_1_81 && var_1_83) || var_1_84))) : 1)))) && (var_1_103 ? (var_1_85 == ((signed char) ((((var_1_46) < (((((var_1_54) < 0 ) ? -(var_1_54) : (var_1_54))))) ? (var_1_46) : (((((var_1_54) < 0 ) ? -(var_1_54) : (var_1_54)))))))) : ((var_1_8 > ((((var_1_10) > (var_1_68)) ? (var_1_10) : (var_1_68)))) ? (var_1_85 == ((signed char) (-16 + var_1_12))) : (var_1_85 == ((signed char) ((((((((var_1_72) > (var_1_12)) ? (var_1_72) : (var_1_12)))) < (var_1_45)) ? (((((var_1_72) > (var_1_12)) ? (var_1_72) : (var_1_12)))) : (var_1_45)))))))) && ((var_1_24 >= var_1_51) ? (var_1_86 == ((signed char) (var_1_12 - var_1_46))) : ((var_1_25 > (var_1_92 / var_1_15)) ? (var_1_86 == ((signed char) (1 - 100))) : (var_1_86 == ((signed char) (var_1_45 - (var_1_87 - var_1_12))))))) && ((var_1_19 > (var_1_22 / var_1_72)) ? (var_1_88 == ((signed char) ((((var_1_45 + var_1_72) < 0 ) ? -(var_1_45 + var_1_72) : (var_1_45 + var_1_72))))) : (var_1_88 == ((signed char) ((((var_1_46) < (var_1_12)) ? (var_1_46) : (var_1_12))))))) && (var_1_89 == ((unsigned long int) ((((var_1_7) < (100000000u)) ? (var_1_7) : (100000000u)))))) && ((var_1_12 <= var_1_87) ? (var_1_90 == ((unsigned char) var_1_37)) : 1)) && (var_1_91 == ((signed short int) var_1_10))) && (var_1_103 ? (var_1_92 == ((signed long int) var_1_54)) : (var_1_92 == ((signed long int) var_1_68)))) && (var_1_93 == ((unsigned char) var_1_75))) && (var_1_94 == ((double) var_1_41))) && (var_1_95 == ((unsigned long int) 2u))) && (var_1_96 == ((unsigned char) var_1_81))) && (var_1_97 == ((unsigned short int) var_1_46))) && (var_1_96 ? (var_1_98 == ((float) var_1_32)) : 1)) && (var_1_99 == ((signed long int) -16))) && (var_1_96 ? (var_1_100 == ((unsigned long int) 256u)) : 1)) && (var_1_79 ? (var_1_101 == ((signed long int) 0)) : 1)) && (var_1_80 ? (var_1_102 == ((double) 10.125)) : (var_1_102 == ((double) var_1_41)))) && (var_1_81 ? (var_1_103 == ((unsigned char) 1)) : 1)) && (var_1_96 ? (var_1_104 == ((unsigned long int) var_1_52)) : 1)) && ((var_1_54 < -5) ? ((var_1_24 < (var_1_52 - (var_1_70 + var_1_66))) ? (var_1_105 == ((unsigned short int) ((((var_1_71) < 0 ) ? -(var_1_71) : (var_1_71))))) : 1) : 1)
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
