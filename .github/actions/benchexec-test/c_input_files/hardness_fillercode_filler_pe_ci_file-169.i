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
void reach_error(void) { __assert_fail("0", "Req1_Prop1_Batch169Filler_PE_CI.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
void initially(void);
void step(void);
void updateVariables(void);
void updateLastVariables(void);
int property(void);
int main(void);
unsigned char isInitial = 0;
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
signed short int last_1_var_1_13 = 100;
void initially(void) {
}
void step(void) {
                                         if ( ((last_1_var_1_13) < ( (( ((var_1_3) - (var_1_4))) / ( (((((var_1_5)) > ((var_1_6))) ? ((var_1_5)) : ((var_1_6))))))))) {
                                          var_1_1 = (
                                           ((
    var_1_3
   ) - (
                                            ((((( ((((( 64 )) > (( var_1_4 ))) ? (( 64 )) : (( var_1_4 )))) )) > (( var_1_7 ))) ? (( ((((( 64 )) > (( var_1_4 ))) ? (( 64 )) : (( var_1_4 )))) )) : (( var_1_7 ))))
   ))
  );
 }
                               if ( ((var_1_4) == ( (~ ( ((var_1_5) + (var_1_1))))))) {
                                var_1_13 = (
   var_1_14
  );
 }
                              if ( ((var_1_6) > (var_1_5))) {
                               var_1_8 = (
                                ((((var_1_3) < 0 ) ? -(var_1_3) : (var_1_3)))
  );
 }
                              var_1_9 = (
                               ((
                                ((((( var_1_10 )) < (( (( 1.000000000000005E14 ) + ( 256.1 )) ))) ? (( var_1_10 )) : (( (( 1.000000000000005E14 ) + ( 256.1 )) ))))
  ) - (
                                ((
    var_1_11
   ) + (
    var_1_12
   ))
  ))
 );
                               if ( ((var_1_14) > ( (((((var_1_1)) > ((-8))) ? ((var_1_1)) : ((-8))))))) {
                                var_1_15 = (
                                 ((((( (( var_1_16 ) + ( ((((( var_1_17 )) > (( var_1_18 ))) ? (( var_1_17 )) : (( var_1_18 )))) )) )) < (( var_1_19 ))) ? (( (( var_1_16 ) + ( ((((( var_1_17 )) > (( var_1_18 ))) ? (( var_1_17 )) : (( var_1_18 )))) )) )) : (( var_1_19 ))))
  );
 } else {
                                var_1_15 = (
                                 ((((( var_1_16 )) < (( var_1_19 ))) ? (( var_1_16 )) : (( var_1_19 ))))
  );
 }
 signed long int stepLocal_0 = (( ((var_1_21) - (var_1_4))) << (var_1_16));
                               if ( ((stepLocal_0) < (var_1_8))) {
                                var_1_20 = (
   var_1_16
  );
 }
                               var_1_22 = (
                                ((
                                 ((((( var_1_4 )) < (( var_1_23 ))) ? (( var_1_4 )) : (( var_1_23 ))))
  ) + (
                                 ((
    var_1_24
   ) + (
    var_1_25
   ))
  ))
 );
 signed long int stepLocal_2 = var_1_8;
 unsigned long int stepLocal_1 = ((5u) >> (16));
                               if ( (( ((8) << (var_1_17))) < (stepLocal_2))) {
                                if ( ((stepLocal_1) > ( ((var_1_28) - ( ((((100u) < 0 ) ? -(100u) : (100u)))))))) {
                                 var_1_26 = (
    var_1_29
   );
  }
 }
                  if ( (( (( (((((var_1_3)) < ((var_1_4))) ? ((var_1_3)) : ((var_1_4))))) - (var_1_4))) <= (var_1_8))) {
                   var_1_30 = (
   var_1_3
  );
 }
                   if ( ((var_1_8) >= ( (((((var_1_3)) < ((var_1_4))) ? ((var_1_3)) : ((var_1_4))))))) {
                    if ( (( (( ((var_1_4) ^ (var_1_8))) * (var_1_8))) >= (var_1_3))) {
                     var_1_35 = (
                      ((((var_1_10) < 0 ) ? -(var_1_10) : (var_1_10)))
   );
  } else {
                     var_1_35 = (
                      (((((( ((((var_1_10) < 0 ) ? -(var_1_10) : (var_1_10))) ) - ( 1.0000000000000005E15f ))) < 0 ) ? -((( ((((var_1_10) < 0 ) ? -(var_1_10) : (var_1_10))) ) - ( 1.0000000000000005E15f ))) : ((( ((((var_1_10) < 0 ) ? -(var_1_10) : (var_1_10))) ) - ( 1.0000000000000005E15f )))))
   );
  }
 }
                   if ( ((var_1_35) >= (var_1_37))) {
                    var_1_38 = (
                     ((((( var_1_23 )) > (( ((((var_1_4) < 0 ) ? -(var_1_4) : (var_1_4))) ))) ? (( var_1_23 )) : (( ((((var_1_4) < 0 ) ? -(var_1_4) : (var_1_4))) ))))
  );
 }
                   var_1_39 = (
  var_1_4
 );
                   if ( (( (~ ( (~ (var_1_4))))) <= (128))) {
                    var_1_40 = (
                     ((((var_1_16) < 0 ) ? -(var_1_16) : (var_1_16)))
  );
 } else {
                    if ( ((var_1_36) && (var_1_42))) {
                     var_1_40 = (
                      ((((((((var_1_16) < 0 ) ? -(var_1_16) : (var_1_16)))) < 0 ) ? -(((((var_1_16) < 0 ) ? -(var_1_16) : (var_1_16)))) : (((((var_1_16) < 0 ) ? -(var_1_16) : (var_1_16))))))
   );
  } else {
                     var_1_40 = (
    var_1_16
   );
  }
 }
                   if ( ((var_1_28) < (var_1_8))) {
                    if ( ((var_1_1) <= ( ((var_1_8) / (-32))))) {
                     var_1_43 = (
                      (((((( var_1_45 ) - ( var_1_46 ))) < 0 ) ? -((( var_1_45 ) - ( var_1_46 ))) : ((( var_1_45 ) - ( var_1_46 )))))
   );
  }
 }
                   if ( (( (( ((var_1_46) - (var_1_48))) / (-2))) < (var_1_18))) {
                    if (var_1_42) {
                     if (var_1_36) {
                      var_1_47 = (
     var_1_4
    );
   }
  } else {
                     var_1_47 = (
    var_1_46
   );
  }
 } else {
                    var_1_47 = (
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
 if ( ((last_1_var_1_13) < ( (( ((var_1_3) - (var_1_4))) / ( (((((var_1_5)) > ((var_1_6))) ? ((var_1_5)) : ((var_1_6))))))))) {
 }
 if ( ((var_1_6) > (var_1_5))) {
 }
 if ( ((var_1_4) == ( (~ ( ((var_1_5) + (var_1_1))))))) {
 }
 if ( ((var_1_14) > ( (((((var_1_1)) > ((-8))) ? ((var_1_1)) : ((-8))))))) {
 } else {
 }
 if ( (( (( ((var_1_21) - (var_1_4))) << (var_1_16))) < (var_1_8))) {
 }
 if ( (( ((8) << (var_1_17))) < (var_1_8))) {
  if ( (( ((5u) >> (16))) > ( ((var_1_28) - ( ((((100u) < 0 ) ? -(100u) : (100u)))))))) {
  }
 }
 return ((
             ((
              ((
               ((
                ((
                 ((
                  ((
                                                     ((
                                                           ((
         last_1_var_1_13
        ) < (
                                                            ((
                                                            ((
           var_1_3
          ) - (
           var_1_4
          ))
         ) / (
                                                             ((((( var_1_5 )) > (( var_1_6 ))) ? (( var_1_5 )) : (( var_1_6 ))))
         ))
        ))
       ) ? (
                                                      ((
         var_1_1
        ) == (
                                                       ((signed long int) (
                                                        ((
           var_1_3
          ) - (
                                                         ((((( ((((( 64 )) > (( var_1_4 ))) ? (( 64 )) : (( var_1_4 )))) )) > (( var_1_7 ))) ? (( ((((( 64 )) > (( var_1_4 ))) ? (( 64 )) : (( var_1_4 )))) )) : (( var_1_7 ))))
          ))
         ))
        ))
       ) : (
        1
       ))
      ) && (
                                          ((
                                                ((
         var_1_6
        ) > (
         var_1_5
        ))
       ) ? (
                                           ((
         var_1_8
        ) == (
                                            ((signed long int) (
                                             ((((var_1_3) < 0 ) ? -(var_1_3) : (var_1_3)))
         ))
        ))
       ) : (
        1
       ))
      ))
     ) && (
                                          ((
       var_1_9
      ) == (
                                           ((double) (
                                            ((
                                             ((((( var_1_10 )) < (( (( 1.000000000000005E14 ) + ( 256.1 )) ))) ? (( var_1_10 )) : (( (( 1.000000000000005E14 ) + ( 256.1 )) ))))
        ) - (
                                             ((
          var_1_11
         ) + (
          var_1_12
         ))
        ))
       ))
      ))
     ))
    ) && (
                                          ((
                                                ((
       var_1_4
      ) == (
                                                 (~ (
                                                  ((
         var_1_5
        ) + (
         var_1_1
        ))
       ))
      ))
     ) ? (
                                           ((
       var_1_13
      ) == (
                                            ((signed short int) (
        var_1_14
       ))
      ))
     ) : (
      1
     ))
    ))
   ) && (
                                         ((
                                                ((
      var_1_14
     ) > (
                                                 ((((( var_1_1 )) > (( -8 ))) ? (( var_1_1 )) : (( -8 ))))
     ))
    ) ? (
                                          ((
      var_1_15
     ) == (
                                           ((signed char) (
                                            ((((( (( var_1_16 ) + ( ((((( var_1_17 )) > (( var_1_18 ))) ? (( var_1_17 )) : (( var_1_18 )))) )) )) < (( var_1_19 ))) ? (( (( var_1_16 ) + ( ((((( var_1_17 )) > (( var_1_18 ))) ? (( var_1_17 )) : (( var_1_18 )))) )) )) : (( var_1_19 ))))
      ))
     ))
    ) : (
                                          ((
      var_1_15
     ) == (
                                           ((signed char) (
                                            ((((( var_1_16 )) < (( var_1_19 ))) ? (( var_1_16 )) : (( var_1_19 ))))
      ))
     ))
    ))
   ))
  ) && (
                                        ((
                                               ((
                                                ((
                                                 ((
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
                                         ((
     var_1_20
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
   var_1_22
  ) == (
                                        ((unsigned short int) (
                                         ((
                                          ((((( var_1_4 )) < (( var_1_23 ))) ? (( var_1_4 )) : (( var_1_23 ))))
    ) + (
                                          ((
      var_1_24
     ) + (
      var_1_25
     ))
    ))
   ))
  ))
 ))
) && (
                                      ((
                                             ((
                                              ((
    8
   ) << (
    var_1_17
   ))
  ) < (
   var_1_8
  ))
 ) ? (
                                       ((
                                              ((
                                               ((
     5u
    ) >> (
     16
    ))
   ) > (
                                               ((
     var_1_28
    ) - (
                                                ((((100u) < 0 ) ? -(100u) : (100u)))
    ))
   ))
  ) ? (
                                        ((
    var_1_26
   ) == (
                                         ((unsigned char) (
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
