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
void reach_error(void) { __assert_fail("0", "Req1_Prop1_Batch167Filler_PE_CI.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
void initially(void);
void step(void);
void updateVariables(void);
void updateLastVariables(void);
int property(void);
int main(void);
unsigned char isInitial = 0;
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
void initially(void) {
}
void step(void) {
 unsigned long int stepLocal_0 = var_1_3;
                              if ( ((stepLocal_0) == ( (((((var_1_4)) > ((var_1_5))) ? ((var_1_4)) : ((var_1_5))))))) {
                               var_1_1 = (
                                ((
                                 ((
                                  ((
      var_1_6
     ) + (
      var_1_7
     ))
    ) + (
                                  ((((( var_1_8 )) < (( var_1_9 ))) ? (( var_1_8 )) : (( var_1_9 ))))
    ))
   ) - (
    var_1_10
   ))
  );
 } else {
                               var_1_1 = (
   8.2f
  );
 }
                              if ( ((var_1_10) > ( ((var_1_7) * ( ((var_1_6) / (var_1_12))))))) {
                               var_1_11 = (
                                ((
    var_1_7
   ) - (
    var_1_9
   ))
  );
 } else {
                               var_1_11 = (
   var_1_8
  );
 }
 unsigned char stepLocal_1 = var_1_15;
                              if ( (( ((var_1_2) && (var_1_14))) && (stepLocal_1))) {
                               var_1_13 = (
   var_1_16
  );
 }
                               var_1_20 = (
                                ((
                                 ((
    var_1_21
   ) + (
    16
   ))
  ) + (
                                 ((
    var_1_22
   ) + (
    var_1_23
   ))
  ))
 );
                               if ( (( (((((var_1_1)) < (( (- (var_1_9))))) ? ((var_1_1)) : (( (- (var_1_9))))))) > (var_1_8))) {
                                if ( (( (( ((((var_1_7) < 0 ) ? -(var_1_7) : (var_1_7)))) / ( (((((var_1_12)) > ((var_1_25))) ? ((var_1_12)) : ((var_1_25))))))) < (var_1_11))) {
                                 var_1_24 = (
                                  ((
     var_1_26
    ) + (
     -2
    ))
   );
  } else {
                                 var_1_24 = (
    var_1_16
   );
  }
 } else {
                                var_1_24 = (
   var_1_26
  );
 }
                               if ( ((var_1_1) >= ( ((((var_1_10) < 0 ) ? -(var_1_10) : (var_1_10)))))) {
                                var_1_27 = (
                                 ((
    var_1_28
   ) || (
    var_1_29
   ))
  );
 } else {
                                var_1_27 = (
   var_1_30
  );
 }
 unsigned long int stepLocal_2 = var_1_5;
                               if ( (( (( (((((var_1_3)) > ((var_1_18))) ? ((var_1_3)) : ((var_1_18))))) * (var_1_4))) == (stepLocal_2))) {
                                var_1_17 = (
                                 ((
    -1
   ) - (
    var_1_19
   ))
  );
 } else {
                                var_1_17 = (
   var_1_24
  );
 }
                  if (var_1_15) {
                  var_1_31 = (
                   ((((var_1_33) < 0 ) ? -(var_1_33) : (var_1_33)))
  );
 }
                  if ( (( ((var_1_33) > (var_1_11))) && (var_1_14))) {
                   var_1_34 = (
                    ((((( var_1_35 )) < (( (( var_1_36 ) + ( var_1_37 )) ))) ? (( var_1_35 )) : (( (( var_1_36 ) + ( var_1_37 )) ))))
  );
 } else {
                   var_1_34 = (
                    ((
    var_1_37
   ) + (
    var_1_36
   ))
  );
 }
                  var_1_38 = (
  var_1_21
 );
                  var_1_40 = (
  var_1_28
 );
                  if ( (( (( (- (var_1_35))) / (var_1_43))) > (var_1_36))) {
                   var_1_42 = (
                    ((((( ((((((((( var_1_21 )) < (( var_1_23 ))) ? (( var_1_21 )) : (( var_1_23 ))))) < 0 ) ? -(((((( var_1_21 )) < (( var_1_23 ))) ? (( var_1_21 )) : (( var_1_23 ))))) : (((((( var_1_21 )) < (( var_1_23 ))) ? (( var_1_21 )) : (( var_1_23 ))))))) )) > (( var_1_43 ))) ? (( ((((((((( var_1_21 )) < (( var_1_23 ))) ? (( var_1_21 )) : (( var_1_23 ))))) < 0 ) ? -(((((( var_1_21 )) < (( var_1_23 ))) ? (( var_1_21 )) : (( var_1_23 ))))) : (((((( var_1_21 )) < (( var_1_23 ))) ? (( var_1_21 )) : (( var_1_23 ))))))) )) : (( var_1_43 ))))
  );
 }
                   if (var_1_30) {
                    var_1_44 = (
                     ((((var_1_33) < 0 ) ? -(var_1_33) : (var_1_33)))
  );
 }
                   var_1_45 = (
                    ((((var_1_33) < 0 ) ? -(var_1_33) : (var_1_33)))
 );
                   if ( ((var_1_21) < ( ((var_1_4) / (10))))) {
                    if ( ((var_1_47) <= (var_1_48))) {
                     var_1_46 = (
    var_1_49
   );
  } else {
                     var_1_46 = (
                      ((((( (( ((((1) < 0 ) ? -(1) : (1))) ) + ( var_1_50 )) )) > (( var_1_49 ))) ? (( (( ((((1) < 0 ) ? -(1) : (1))) ) + ( var_1_50 )) )) : (( var_1_49 ))))
   );
  }
 } else {
                    if ( ((var_1_4) >= (var_1_5))) {
                     var_1_46 = (
                      ((((((((( var_1_49 )) > (( var_1_50 ))) ? (( var_1_49 )) : (( var_1_50 ))))) < 0 ) ? -(((((( var_1_49 )) > (( var_1_50 ))) ? (( var_1_49 )) : (( var_1_50 ))))) : (((((( var_1_49 )) > (( var_1_50 ))) ? (( var_1_49 )) : (( var_1_50 )))))))
   );
  } else {
                     var_1_46 = (
    var_1_49
   );
  }
 }
                   if ( (( (( ((var_1_23) - (var_1_50))) & (var_1_3))) >= ( (( (((((var_1_52)) > ((var_1_53))) ? ((var_1_52)) : ((var_1_53))))) - (var_1_43))))) {
                    if ( ((var_1_49) > (var_1_21))) {
                     var_1_51 = (
    var_1_49
   );
  } else {
                     var_1_51 = (
    var_1_43
   );
  }
 } else {
                    var_1_51 = (
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
 if ( ((var_1_3) == ( (((((var_1_4)) > ((var_1_5))) ? ((var_1_4)) : ((var_1_5))))))) {
 } else {
 }
 if ( ((var_1_10) > ( ((var_1_7) * ( ((var_1_6) / (var_1_12))))))) {
 } else {
 }
 if ( (( ((var_1_2) && (var_1_14))) && (var_1_15))) {
 }
 if ( (( (( (((((var_1_3)) > ((var_1_18))) ? ((var_1_3)) : ((var_1_18))))) * (var_1_4))) == (var_1_5))) {
 } else {
 }
 if ( (( (((((var_1_1)) < (( (- (var_1_9))))) ? ((var_1_1)) : (( (- (var_1_9))))))) > (var_1_8))) {
  if ( (( (( ((((var_1_7) < 0 ) ? -(var_1_7) : (var_1_7)))) / ( (((((var_1_12)) > ((var_1_25))) ? ((var_1_12)) : ((var_1_25))))))) < (var_1_11))) {
  } else {
  }
 } else {
 }
 if ( ((var_1_1) >= ( ((((var_1_10) < 0 ) ? -(var_1_10) : (var_1_10)))))) {
 } else {
 }
 return ((
             ((
              ((
               ((
                ((
                 ((
                                         ((
                                              ((
        var_1_3
       ) == (
                                               ((((( var_1_4 )) > (( var_1_5 ))) ? (( var_1_4 )) : (( var_1_5 ))))
       ))
      ) ? (
                                          ((
        var_1_1
       ) == (
                                           ((float) (
                                            ((
                                             ((
                                              ((
            var_1_6
           ) + (
            var_1_7
           ))
          ) + (
                                              ((((( var_1_8 )) < (( var_1_9 ))) ? (( var_1_8 )) : (( var_1_9 ))))
          ))
         ) - (
          var_1_10
         ))
        ))
       ))
      ) : (
                                          ((
        var_1_1
       ) == (
                                           ((float) (
         8.2f
        ))
       ))
      ))
     ) && (
                                         ((
                                               ((
        var_1_10
       ) > (
                                                ((
         var_1_7
        ) * (
                                                 ((
          var_1_6
         ) / (
          var_1_12
         ))
        ))
       ))
      ) ? (
                                          ((
        var_1_11
       ) == (
                                           ((double) (
                                            ((
          var_1_7
         ) - (
          var_1_9
         ))
        ))
       ))
      ) : (
                                          ((
        var_1_11
       ) == (
                                           ((double) (
         var_1_8
        ))
       ))
      ))
     ))
    ) && (
                                        ((
                                              ((
                                               ((
        var_1_2
       ) && (
        var_1_14
       ))
      ) && (
       var_1_15
      ))
     ) ? (
                                         ((
       var_1_13
      ) == (
                                          ((signed char) (
        var_1_16
       ))
      ))
     ) : (
      1
     ))
    ))
   ) && (
                                        ((
                                               ((
                                                ((
                                                 ((((( var_1_3 )) > (( var_1_18 ))) ? (( var_1_3 )) : (( var_1_18 ))))
      ) * (
       var_1_4
      ))
     ) == (
      var_1_5
     ))
    ) ? (
                                          ((
      var_1_17
     ) == (
                                           ((signed short int) (
                                            ((
        -1
       ) - (
        var_1_19
       ))
      ))
     ))
    ) : (
                                          ((
      var_1_17
     ) == (
                                           ((signed short int) (
       var_1_24
      ))
     ))
    ))
   ))
  ) && (
                                        ((
    var_1_20
   ) == (
                                         ((unsigned short int) (
                                          ((
                                           ((
       var_1_21
      ) + (
       16
      ))
     ) + (
                                           ((
       var_1_22
      ) + (
       var_1_23
      ))
     ))
    ))
   ))
  ))
 ) && (
                                       ((
                                              ((
                                               ((((( var_1_1 )) < (( (- ( var_1_9 )) ))) ? (( var_1_1 )) : (( (- ( var_1_9 )) ))))
   ) > (
    var_1_8
   ))
  ) ? (
                                        ((
                                               ((
                                                ((
                                                 ((((var_1_7) < 0 ) ? -(var_1_7) : (var_1_7)))
     ) / (
                                                 ((((( var_1_12 )) > (( var_1_25 ))) ? (( var_1_12 )) : (( var_1_25 ))))
     ))
    ) < (
     var_1_11
    ))
   ) ? (
                                         ((
     var_1_24
    ) == (
                                          ((signed char) (
                                           ((
       var_1_26
      ) + (
       -2
      ))
     ))
    ))
   ) : (
                                         ((
     var_1_24
    ) == (
                                          ((signed char) (
      var_1_16
     ))
    ))
   ))
  ) : (
                                        ((
    var_1_24
   ) == (
                                         ((signed char) (
     var_1_26
    ))
   ))
  ))
 ))
) && (
                                      ((
                                             ((
   var_1_1
  ) >= (
                                              ((((var_1_10) < 0 ) ? -(var_1_10) : (var_1_10)))
  ))
 ) ? (
                                       ((
   var_1_27
  ) == (
                                        ((unsigned char) (
                                         ((
     var_1_28
    ) || (
     var_1_29
    ))
   ))
  ))
 ) : (
                                       ((
   var_1_27
  ) == (
                                        ((unsigned char) (
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
