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
void reach_error(void) { __assert_fail("0", "Req1_Prop1_Batch153Filler_PE_CI.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
void initially(void);
void step(void);
void updateVariables(void);
void updateLastVariables(void);
int property(void);
int main(void);
unsigned char isInitial = 0;
double var_1_1 = -0.875;
unsigned char var_1_2 = 1;
signed short int var_1_3 = 500;
signed short int var_1_4 = 256;
signed long int var_1_5 = 4;
double var_1_7 = 1000.2;
double var_1_8 = 127.875;
double var_1_9 = 99999.25;
signed short int var_1_10 = 16;
signed char var_1_11 = -8;
double var_1_12 = 16.6;
double var_1_13 = 500.28;
signed char var_1_14 = -64;
signed long int var_1_15 = -25;
unsigned char var_1_16 = 128;
unsigned char var_1_17 = 64;
signed char var_1_18 = -16;
unsigned char var_1_19 = 1;
signed char var_1_20 = -8;
signed char var_1_21 = 2;
signed char var_1_22 = 50;
signed char var_1_23 = 10;
float var_1_24 = 25.4;
float var_1_25 = 2.775;
float var_1_26 = 256.8;
float var_1_27 = 1.2;
double var_1_28 = 32.5;
unsigned char var_1_29 = 1;
unsigned char var_1_30 = 1;
unsigned char var_1_31 = 0;
signed char var_1_32 = -64;
signed long int var_1_34 = 1985949473;
unsigned long int var_1_35 = 25;
signed char var_1_36 = -16;
float var_1_38 = -0.05;
signed long int var_1_41 = 4;
float var_1_42 = 128.75;
double var_1_44 = 31.75;
signed short int last_1_var_1_10 = 16;
signed char last_1_var_1_14 = -64;
void initially(void) {
}
void step(void) {
 signed long int stepLocal_2 = last_1_var_1_10;
                                          if ( (( ((var_1_16) - ( ((var_1_17) - (var_1_5))))) <= (stepLocal_2))) {
                                           var_1_15 = (
   last_1_var_1_14
  );
 }
                              if (var_1_2) {
                               if ( (( (( ((var_1_3) + (var_1_4))) << (var_1_5))) > (var_1_15))) {
                                var_1_1 = (
    var_1_7
   );
  } else {
                                var_1_1 = (
                                 ((
     1.06
    ) + (
                                  ((((( var_1_8 )) > (( var_1_9 ))) ? (( var_1_8 )) : (( var_1_9 ))))
    ))
   );
  }
 } else {
                               if ( (( (( ((var_1_9) + (255.72))) / (128.5))) < ( (( (- (var_1_8))) * (var_1_7))))) {
                                var_1_1 = (
    var_1_9
   );
  } else {
                                var_1_1 = (
    var_1_7
   );
  }
 }
                               if ( ((var_1_1) < ( ((var_1_8) * ( (((((var_1_9)) > ((var_1_7))) ? ((var_1_9)) : ((var_1_7))))))))) {
                                var_1_10 = (
                                 ((
    var_1_5
   ) - (
                                  ((((( (( 32476 ) - ( var_1_4 )) )) < (( 8 ))) ? (( (( 32476 ) - ( var_1_4 )) )) : (( 8 ))))
   ))
  );
 }
                               if ( ((var_1_15) <= (var_1_4))) {
                                if ( (! ( ((var_1_15) <= (var_1_5))))) {
                                 if ( (( ((var_1_4) & (var_1_5))) >= (var_1_15))) {
                                  var_1_14 = (
     var_1_5
    );
   }
  }
 }
 signed long int stepLocal_0 = ((var_1_15) + (var_1_3));
                               if ( ((var_1_15) >= (stepLocal_0))) {
                                var_1_11 = (
                                 ((((var_1_5) < 0 ) ? -(var_1_5) : (var_1_5)))
  );
 } else {
                                var_1_11 = (
   var_1_5
  );
 }
 signed long int stepLocal_1 = var_1_15;
                               if ( (( ((var_1_5) + (var_1_4))) < (stepLocal_1))) {
                                var_1_12 = (
                                 ((
    var_1_13
   ) + (
    var_1_9
   ))
  );
 } else {
                                var_1_12 = (
   var_1_7
  );
 }
                  if (var_1_2) {
                   var_1_18 = (
                    ((((( (( ((((-10) < 0 ) ? -(-10) : (-10))) ) + ( var_1_20 )) )) < (( (( var_1_21 ) + ( (( var_1_22 ) - ( var_1_23 )) )) ))) ? (( (( ((((-10) < 0 ) ? -(-10) : (-10))) ) + ( var_1_20 )) )) : (( (( var_1_21 ) + ( (( var_1_22 ) - ( var_1_23 )) )) ))))
  );
 }
                  if ( (( (((((((((var_1_25)) < ((var_1_26))) ? ((var_1_25)) : ((var_1_26))))) < 0 ) ? -((((((var_1_25)) < ((var_1_26))) ? ((var_1_25)) : ((var_1_26))))) : ((((((var_1_25)) < ((var_1_26))) ? ((var_1_25)) : ((var_1_26)))))))) >= (9.25f))) {
                   var_1_24 = (
                    ((((var_1_27) < 0 ) ? -(var_1_27) : (var_1_27)))
  );
 }
                   if (var_1_19) {
                    if (var_1_29) {
                     if ( ((var_1_30) || (var_1_31))) {
                      var_1_28 = (
     var_1_9
    );
   }
  }
 }
                   if ( (( ((var_1_15) / (var_1_17))) > (var_1_5))) {
                    if ( (( ((((var_1_17) < 0 ) ? -(var_1_17) : (var_1_17)))) < ( (( ((var_1_34) - (var_1_5))) >> (var_1_35))))) {
                     var_1_32 = (
                      ((((((((var_1_5) < 0 ) ? -(var_1_5) : (var_1_5)))) < 0 ) ? -(((((var_1_5) < 0 ) ? -(var_1_5) : (var_1_5)))) : (((((var_1_5) < 0 ) ? -(var_1_5) : (var_1_5))))))
   );
  }
 }
                   if ( (( (- (var_1_9))) >= (var_1_9))) {
                    var_1_36 = (
                     ((
    var_1_21
   ) + (
    var_1_23
   ))
  );
 } else {
                    var_1_36 = (
                     ((
    var_1_20
   ) + (
    var_1_23
   ))
  );
 }
                   var_1_38 = (
                    ((((( (( var_1_13 ) + ( var_1_9 )) )) < (( var_1_9 ))) ? (( (( var_1_13 ) + ( var_1_9 )) )) : (( var_1_9 ))))
 );
                   if ( ((var_1_8) >= ( (((((var_1_7)) > (( ((var_1_7) / (var_1_42))))) ? ((var_1_7)) : (( ((var_1_7) / (var_1_42))))))))) {
                    var_1_41 = (
                     ((((( (( (( 32 ) + ( var_1_5 )) ) + ( var_1_5 )) )) > (( var_1_16 ))) ? (( (( (( 32 ) + ( var_1_5 )) ) + ( var_1_5 )) )) : (( var_1_16 ))))
  );
 } else {
                    var_1_41 = (
                     ((((( -50 )) < (( var_1_5 ))) ? (( -50 )) : (( var_1_5 ))))
  );
 }
                   var_1_44 = (
  var_1_13
 );
}
void updateVariables(void) {
 var_1_2 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_2 >= 0);
 assume_abort_if_not(var_1_2 <= 1);
 var_1_3 = __VERIFIER_nondet_short();
 assume_abort_if_not(var_1_3 >= 0);
 assume_abort_if_not(var_1_3 <= 16384);
 var_1_4 = __VERIFIER_nondet_short();
 assume_abort_if_not(var_1_4 >= 0);
 assume_abort_if_not(var_1_4 <= 16383);
 var_1_5 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_5 >= 0);
 assume_abort_if_not(var_1_5 <= 16);
 var_1_7 = __VERIFIER_nondet_double();
 assume_abort_if_not((var_1_7 >= -922337.2036854766000e+13F && var_1_7 <= -1.0e-20F) || (var_1_7 <= 9223372.036854766000e+12F && var_1_7 >= 1.0e-20F ));
 var_1_8 = __VERIFIER_nondet_double();
 assume_abort_if_not((var_1_8 >= -461168.6018427383000e+13F && var_1_8 <= -1.0e-20F) || (var_1_8 <= 4611686.018427383000e+12F && var_1_8 >= 1.0e-20F ));
 var_1_9 = __VERIFIER_nondet_double();
 assume_abort_if_not((var_1_9 >= -461168.6018427383000e+13F && var_1_9 <= -1.0e-20F) || (var_1_9 <= 4611686.018427383000e+12F && var_1_9 >= 1.0e-20F ));
 var_1_13 = __VERIFIER_nondet_double();
 assume_abort_if_not((var_1_13 >= -461168.6018427383000e+13F && var_1_13 <= -1.0e-20F) || (var_1_13 <= 4611686.018427383000e+12F && var_1_13 >= 1.0e-20F ));
 var_1_16 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_16 >= 127);
 assume_abort_if_not(var_1_16 <= 255);
 var_1_17 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_17 >= 63);
 assume_abort_if_not(var_1_17 <= 127);
 var_1_19 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_19 >= 0);
 assume_abort_if_not(var_1_19 <= 1);
 var_1_20 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_20 >= -63);
 assume_abort_if_not(var_1_20 <= 63);
 var_1_21 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_21 >= -63);
 assume_abort_if_not(var_1_21 <= 63);
 var_1_22 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_22 >= 0);
 assume_abort_if_not(var_1_22 <= 63);
 var_1_23 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_23 >= 0);
 assume_abort_if_not(var_1_23 <= 63);
 var_1_25 = __VERIFIER_nondet_float();
 assume_abort_if_not((var_1_25 >= -922337.2036854776000e+13F && var_1_25 <= -1.0e-20F) || (var_1_25 <= 9223372.036854776000e+12F && var_1_25 >= 1.0e-20F ));
 var_1_26 = __VERIFIER_nondet_float();
 assume_abort_if_not((var_1_26 >= -922337.2036854776000e+13F && var_1_26 <= -1.0e-20F) || (var_1_26 <= 9223372.036854776000e+12F && var_1_26 >= 1.0e-20F ));
 var_1_27 = __VERIFIER_nondet_float();
 assume_abort_if_not((var_1_27 >= -922337.2036854766000e+13F && var_1_27 <= -1.0e-20F) || (var_1_27 <= 9223372.036854766000e+12F && var_1_27 >= 1.0e-20F ));
 var_1_29 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_29 >= 0);
 assume_abort_if_not(var_1_29 <= 1);
 var_1_30 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_30 >= 0);
 assume_abort_if_not(var_1_30 <= 1);
 var_1_31 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_31 >= 0);
 assume_abort_if_not(var_1_31 <= 1);
 var_1_34 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_34 >= 1073741823);
 assume_abort_if_not(var_1_34 <= 2147483647);
 var_1_35 = __VERIFIER_nondet_ulong();
 assume_abort_if_not(var_1_35 >= 1);
 assume_abort_if_not(var_1_35 <= 30);
 var_1_42 = __VERIFIER_nondet_float();
 assume_abort_if_not((var_1_42 >= -922337.2036854776000e+13F && var_1_42 <= -1.0e-20F) || (var_1_42 <= 9223372.036854776000e+12F && var_1_42 >= 1.0e-20F ));
 assume_abort_if_not(var_1_42 != 0.0F);
}
void updateLastVariables(void) {
 last_1_var_1_10 = var_1_10;
 last_1_var_1_14 = var_1_14;
}
int property(void) {
 if (var_1_2) {
  if ( (( (( ((var_1_3) + (var_1_4))) << (var_1_5))) > (var_1_15))) {
  } else {
  }
 } else {
  if ( (( (( ((var_1_9) + (255.72))) / (128.5))) < ( (( (- (var_1_8))) * (var_1_7))))) {
  } else {
  }
 }
 if ( ((var_1_1) < ( ((var_1_8) * ( (((((var_1_9)) > ((var_1_7))) ? ((var_1_9)) : ((var_1_7))))))))) {
 }
 if ( ((var_1_15) >= ( ((var_1_15) + (var_1_3))))) {
 } else {
 }
 if ( (( ((var_1_5) + (var_1_4))) < (var_1_15))) {
 } else {
 }
 if ( ((var_1_15) <= (var_1_4))) {
  if ( (! ( ((var_1_15) <= (var_1_5))))) {
   if ( (( ((var_1_4) & (var_1_5))) >= (var_1_15))) {
   }
  }
 }
 if ( (( ((var_1_16) - ( ((var_1_17) - (var_1_5))))) <= (last_1_var_1_10))) {
 }
 return ((
             ((
              ((
               ((
                ((
                                        ((
      var_1_2
     ) ? (
                                         ((
                                               ((
                                               ((
                                                ((
          var_1_3
         ) + (
          var_1_4
         ))
        ) << (
         var_1_5
        ))
       ) > (
        var_1_15
       ))
      ) ? (
                                          ((
        var_1_1
       ) == (
                                           ((double) (
         var_1_7
        ))
       ))
      ) : (
                                          ((
        var_1_1
       ) == (
                                           ((double) (
                                            ((
          1.06
         ) + (
                                             ((((( var_1_8 )) > (( var_1_9 ))) ? (( var_1_8 )) : (( var_1_9 ))))
         ))
        ))
       ))
      ))
     ) : (
                                         ((
                                               ((
                                                ((
                                                 ((
          var_1_9
         ) + (
          255.72
         ))
        ) / (
         128.5
        ))
       ) < (
                                                 ((
                                                  (- (
          var_1_8
         ))
        ) * (
         var_1_7
        ))
       ))
      ) ? (
                                           ((
        var_1_1
       ) == (
                                            ((double) (
         var_1_9
        ))
       ))
      ) : (
                                           ((
        var_1_1
       ) == (
                                            ((double) (
         var_1_7
        ))
       ))
      ))
     ))
    ) && (
                                          ((
                                                ((
       var_1_1
      ) < (
                                                 ((
        var_1_8
       ) * (
                                                  ((((( var_1_9 )) > (( var_1_7 ))) ? (( var_1_9 )) : (( var_1_7 ))))
       ))
      ))
     ) ? (
                                           ((
       var_1_10
      ) == (
                                            ((signed short int) (
                                             ((
         var_1_5
        ) - (
                                              ((((( (( 32476 ) - ( var_1_4 )) )) < (( 8 ))) ? (( (( 32476 ) - ( var_1_4 )) )) : (( 8 ))))
        ))
       ))
      ))
     ) : (
      1
     ))
    ))
   ) && (
                                         ((
                                                ((
      var_1_15
     ) >= (
                                                 ((
       var_1_15
      ) + (
       var_1_3
      ))
     ))
    ) ? (
                                          ((
      var_1_11
     ) == (
                                           ((signed char) (
                                            ((((var_1_5) < 0 ) ? -(var_1_5) : (var_1_5)))
      ))
     ))
    ) : (
                                          ((
      var_1_11
     ) == (
                                           ((signed char) (
       var_1_5
      ))
     ))
    ))
   ))
  ) && (
                                        ((
                                               ((
                                                ((
      var_1_5
     ) + (
      var_1_4
     ))
    ) < (
     var_1_15
    ))
   ) ? (
                                         ((
     var_1_12
    ) == (
                                          ((double) (
                                           ((
       var_1_13
      ) + (
       var_1_9
      ))
     ))
    ))
   ) : (
                                         ((
     var_1_12
    ) == (
                                          ((double) (
      var_1_7
     ))
    ))
   ))
  ))
 ) && (
                                       ((
                                              ((
    var_1_15
   ) <= (
    var_1_4
   ))
  ) ? (
                                        ((
                                               (! (
                                                ((
      var_1_15
     ) <= (
      var_1_5
     ))
    ))
   ) ? (
                                         ((
                                                ((
                                                 ((
       var_1_4
      ) & (
       var_1_5
      ))
     ) >= (
      var_1_15
     ))
    ) ? (
                                          ((
      var_1_14
     ) == (
                                           ((signed char) (
       var_1_5
      ))
     ))
    ) : (
     1
    ))
   ) : (
    1
   ))
  ) : (
   1
  ))
 ))
) && (
                                                 ((
                                                        ((
                                                         ((
    var_1_16
   ) - (
                                                          ((
     var_1_17
    ) - (
     var_1_5
    ))
   ))
  ) <= (
   last_1_var_1_10
  ))
 ) ? (
                                                  ((
   var_1_15
  ) == (
                                                   ((signed long int) (
    last_1_var_1_14
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
