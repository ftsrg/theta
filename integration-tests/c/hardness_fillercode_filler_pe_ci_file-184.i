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
void reach_error(void) { __assert_fail("0", "Req1_Prop1_Batch184Filler_PE_CI.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
void initially(void);
void step(void);
void updateVariables(void);
void updateLastVariables(void);
int property(void);
int main(void);
unsigned char isInitial = 0;
unsigned char var_1_1 = 1;
unsigned char var_1_2 = 100;
unsigned char var_1_3 = 100;
unsigned char var_1_4 = 100;
signed long int var_1_5 = -4;
unsigned char var_1_6 = 0;
unsigned char var_1_7 = 0;
unsigned char var_1_8 = 4;
unsigned char var_1_9 = 128;
unsigned char var_1_10 = 200;
unsigned char var_1_11 = 2;
double var_1_12 = 128.75;
double var_1_13 = 499.9;
double var_1_14 = 127.6;
double var_1_15 = 7.5;
double var_1_16 = 15.25;
unsigned char var_1_17 = 1;
double var_1_18 = 0.09999999999999998;
double var_1_19 = 1.375;
float var_1_20 = 100000000000000.5;
unsigned short int var_1_22 = 200;
signed long int var_1_23 = -10;
signed long int var_1_24 = -10;
unsigned long int var_1_25 = 64;
signed long int var_1_26 = -32;
unsigned long int var_1_29 = 256;
float var_1_30 = 8.4;
double var_1_32 = 256.75;
signed char var_1_34 = -5;
signed char var_1_35 = 50;
signed char var_1_36 = 32;
signed char var_1_37 = 16;
signed char var_1_38 = 8;
signed char var_1_39 = 2;
signed char var_1_40 = -16;
unsigned char var_1_41 = 0;
unsigned char var_1_42 = 1;
unsigned char var_1_43 = 5;
unsigned char var_1_45 = 0;
unsigned char var_1_46 = 25;
unsigned long int var_1_47 = 0;
unsigned char var_1_48 = 10;
unsigned short int var_1_49 = 32;
void initially(void) {
}
void step(void) {
 signed long int stepLocal_0 = var_1_5;
                              if ( ((var_1_4) <= (stepLocal_0))) {
                               var_1_8 = (
                                ((
                                 ((((( var_1_9 )) < (( var_1_10 ))) ? (( var_1_9 )) : (( var_1_10 ))))
   ) - (
                                 ((
     64
    ) - (
     var_1_11
    ))
   ))
  );
 } else {
                               var_1_8 = (
                                ((((( ((((( var_1_9 )) < (( var_1_11 ))) ? (( var_1_9 )) : (( var_1_11 )))) )) > (( var_1_10 ))) ? (( ((((( var_1_9 )) < (( var_1_11 ))) ? (( var_1_9 )) : (( var_1_11 )))) )) : (( var_1_10 ))))
  );
 }
 signed long int stepLocal_1 = var_1_5;
                               if ( (( (( ((var_1_10) | (var_1_4))) * (var_1_8))) <= (stepLocal_1))) {
                                var_1_12 = (
                                 ((
    var_1_13
   ) - (
    var_1_14
   ))
  );
 } else {
                                var_1_12 = (
                                 ((
    var_1_15
   ) + (
    var_1_16
   ))
  );
 }
                               if ( ((var_1_14) <= ( (((((var_1_13)) > (( ((var_1_18) - (var_1_19))))) ? ((var_1_13)) : (( ((var_1_18) - (var_1_19))))))))) {
                                var_1_17 = (
   var_1_6
  );
 }
                              if ( (( ((var_1_8) / ( (((((var_1_3)) < ((var_1_4))) ? ((var_1_3)) : ((var_1_4))))))) <= (var_1_5))) {
                               if ( ((var_1_4) >= (100))) {
                                var_1_1 = (
    var_1_6
   );
  } else {
                                if (var_1_6) {
                                 var_1_1 = (
     var_1_7
    );
   } else {
                                 var_1_1 = (
     0
    );
   }
  }
 } else {
                               var_1_1 = (
   0
  );
 }
 unsigned char stepLocal_2 = var_1_7;
                               if ( ((stepLocal_2) || ( ((var_1_17) || (var_1_6))))) {
                                if (var_1_1) {
                                 var_1_20 = (
                                  ((((( var_1_15 )) < (( ((((var_1_16) < 0 ) ? -(var_1_16) : (var_1_16))) ))) ? (( var_1_15 )) : (( ((((var_1_16) < 0 ) ? -(var_1_16) : (var_1_16))) ))))
   );
  }
 } else {
                                var_1_20 = (
                                 ((
    var_1_16
   ) + (
    var_1_15
   ))
  );
 }
                               if ( (! (var_1_1))) {
                                var_1_22 = (
                                  ((((((((( var_1_8 )) < (( var_1_2 ))) ? (( var_1_8 )) : (( var_1_2 ))))) < 0 ) ? -(((((( var_1_8 )) < (( var_1_2 ))) ? (( var_1_8 )) : (( var_1_2 ))))) : (((((( var_1_8 )) < (( var_1_2 ))) ? (( var_1_8 )) : (( var_1_2 )))))))
  );
 } else {
                                 if ( ((1) < ( ((var_1_3) + (var_1_5))))) {
                                  var_1_22 = (
    var_1_9
   );
  } else {
                                  var_1_22 = (
    var_1_8
   );
  }
 }
                 var_1_23 = (
  var_1_24
 );
                  if ( ((var_1_24) > ( ((((var_1_26) < 0 ) ? -(var_1_26) : (var_1_26)))))) {
                   if ( ((var_1_1) && (var_1_7))) {
                    var_1_25 = (
    var_1_29
   );
  }
 }
                  var_1_30 = (
  var_1_14
 );
                  if ( (( (- ( ((var_1_26) ^ (var_1_25))))) < ( ((((var_1_29) < 0 ) ? -(var_1_29) : (var_1_29)))))) {
                   var_1_32 = (
                    ((((var_1_14) < 0 ) ? -(var_1_14) : (var_1_14)))
  );
 }
                   if ( ((var_1_29) <= (var_1_5))) {
                    if ( (( ((var_1_24) & (var_1_29))) > (var_1_5))) {
                     var_1_34 = (
                      ((
                       ((((( ((((( var_1_35 )) > (( var_1_36 ))) ? (( var_1_35 )) : (( var_1_36 )))) )) > (( var_1_37 ))) ? (( ((((( var_1_35 )) > (( var_1_36 ))) ? (( var_1_35 )) : (( var_1_36 )))) )) : (( var_1_37 ))))
    ) + (
     var_1_38
    ))
   );
  }
 } else {
                    var_1_34 = (
                     ((((( (( var_1_39 ) - ( ((((var_1_38) < 0 ) ? -(var_1_38) : (var_1_38))) )) )) > (( (( var_1_36 ) + ( var_1_40 )) ))) ? (( (( var_1_39 ) - ( ((((var_1_38) < 0 ) ? -(var_1_38) : (var_1_38))) )) )) : (( (( var_1_36 ) + ( var_1_40 )) ))))
  );
 }
                   if ( ((var_1_11) > ( ((((var_1_11) < 0 ) ? -(var_1_11) : (var_1_11)))))) {
                    var_1_41 = (
                     ((
    var_1_7
   ) || (
    var_1_42
   ))
  );
 }
                   if ( ((var_1_5) <= ( ((var_1_36) ^ ( ((-4) ^ (var_1_25))))))) {
                    var_1_43 = (
                     ((((( var_1_10 )) < (( (( var_1_45 ) + ( var_1_46 )) ))) ? (( var_1_10 )) : (( (( var_1_45 ) + ( var_1_46 )) ))))
  );
 }
                   if (var_1_17) {
                    var_1_47 = (
                     ((((( 1u )) > (( var_1_10 ))) ? (( 1u )) : (( var_1_10 ))))
  );
 } else {
                    if ( ((var_1_11) > ( (((((-2)) > ((var_1_11))) ? ((-2)) : ((var_1_11))))))) {
                     var_1_47 = (
    var_1_11
   );
  }
 }
                   var_1_48 = (
  var_1_11
 );
                   var_1_49 = (
  var_1_10
 );
}
void updateVariables(void) {
 var_1_2 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_2 >= 0);
 assume_abort_if_not(var_1_2 <= 255);
 var_1_3 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_3 >= 0);
 assume_abort_if_not(var_1_3 <= 255);
 assume_abort_if_not(var_1_3 != 0);
 var_1_4 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_4 >= 0);
 assume_abort_if_not(var_1_4 <= 255);
 assume_abort_if_not(var_1_4 != 0);
 var_1_5 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_5 >= -2147483648);
 assume_abort_if_not(var_1_5 <= 2147483647);
 var_1_6 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_6 >= 1);
 assume_abort_if_not(var_1_6 <= 1);
 var_1_7 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_7 >= 0);
 assume_abort_if_not(var_1_7 <= 0);
 var_1_9 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_9 >= 127);
 assume_abort_if_not(var_1_9 <= 254);
 var_1_10 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_10 >= 127);
 assume_abort_if_not(var_1_10 <= 254);
 var_1_11 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_11 >= 0);
 assume_abort_if_not(var_1_11 <= 63);
 var_1_13 = __VERIFIER_nondet_double();
 assume_abort_if_not((var_1_13 >= 0.0F && var_1_13 <= -1.0e-20F) || (var_1_13 <= 9223372.036854766000e+12F && var_1_13 >= 1.0e-20F ));
 var_1_14 = __VERIFIER_nondet_double();
 assume_abort_if_not((var_1_14 >= 0.0F && var_1_14 <= -1.0e-20F) || (var_1_14 <= 9223372.036854766000e+12F && var_1_14 >= 1.0e-20F ));
 var_1_15 = __VERIFIER_nondet_double();
 assume_abort_if_not((var_1_15 >= -461168.6018427383000e+13F && var_1_15 <= -1.0e-20F) || (var_1_15 <= 4611686.018427383000e+12F && var_1_15 >= 1.0e-20F ));
 var_1_16 = __VERIFIER_nondet_double();
 assume_abort_if_not((var_1_16 >= -461168.6018427383000e+13F && var_1_16 <= -1.0e-20F) || (var_1_16 <= 4611686.018427383000e+12F && var_1_16 >= 1.0e-20F ));
 var_1_18 = __VERIFIER_nondet_double();
 assume_abort_if_not((var_1_18 >= 0.0F && var_1_18 <= -1.0e-20F) || (var_1_18 <= 9223372.036854776000e+12F && var_1_18 >= 1.0e-20F ));
 var_1_19 = __VERIFIER_nondet_double();
 assume_abort_if_not((var_1_19 >= 0.0F && var_1_19 <= -1.0e-20F) || (var_1_19 <= 9223372.036854776000e+12F && var_1_19 >= 1.0e-20F ));
 var_1_24 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_24 >= -2147483647);
 assume_abort_if_not(var_1_24 <= 2147483646);
 var_1_26 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_26 >= -2147483647);
 assume_abort_if_not(var_1_26 <= 2147483647);
 var_1_29 = __VERIFIER_nondet_ulong();
 assume_abort_if_not(var_1_29 >= 0);
 assume_abort_if_not(var_1_29 <= 4294967294);
 var_1_35 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_35 >= -63);
 assume_abort_if_not(var_1_35 <= 63);
 var_1_36 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_36 >= -63);
 assume_abort_if_not(var_1_36 <= 63);
 var_1_37 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_37 >= -63);
 assume_abort_if_not(var_1_37 <= 63);
 var_1_38 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_38 >= -63);
 assume_abort_if_not(var_1_38 <= 63);
 var_1_39 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_39 >= -1);
 assume_abort_if_not(var_1_39 <= 126);
 var_1_40 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_40 >= -63);
 assume_abort_if_not(var_1_40 <= 63);
 var_1_42 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_42 >= 1);
 assume_abort_if_not(var_1_42 <= 1);
 var_1_45 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_45 >= 0);
 assume_abort_if_not(var_1_45 <= 127);
 var_1_46 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_46 >= 0);
 assume_abort_if_not(var_1_46 <= 127);
}
void updateLastVariables(void) {
}
int property(void) {
 if ( (( ((var_1_8) / ( (((((var_1_3)) < ((var_1_4))) ? ((var_1_3)) : ((var_1_4))))))) <= (var_1_5))) {
  if ( ((var_1_4) >= (100))) {
  } else {
   if (var_1_6) {
   } else {
   }
  }
 } else {
 }
 if ( ((var_1_4) <= (var_1_5))) {
 } else {
 }
 if ( (( (( ((var_1_10) | (var_1_4))) * (var_1_8))) <= (var_1_5))) {
 } else {
 }
 if ( ((var_1_14) <= ( (((((var_1_13)) > (( ((var_1_18) - (var_1_19))))) ? ((var_1_13)) : (( ((var_1_18) - (var_1_19))))))))) {
 }
 if ( ((var_1_7) || ( ((var_1_17) || (var_1_6))))) {
  if (var_1_1) {
  }
 } else {
 }
 if ( (! (var_1_1))) {
 } else {
  if ( ((1) < ( ((var_1_3) + (var_1_5))))) {
  } else {
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
        var_1_8
       ) / (
                                                ((((( var_1_3 )) < (( var_1_4 ))) ? (( var_1_3 )) : (( var_1_4 ))))
       ))
      ) <= (
       var_1_5
      ))
     ) ? (
                                          ((
                                                ((
        var_1_4
       ) >= (
        100
       ))
      ) ? (
                                           ((
        var_1_1
       ) == (
                                            ((unsigned char) (
         var_1_6
        ))
       ))
      ) : (
                                           ((
        var_1_6
       ) ? (
                                            ((
         var_1_1
        ) == (
                                             ((unsigned char) (
          var_1_7
         ))
        ))
       ) : (
                                            ((
         var_1_1
        ) == (
                                             ((unsigned char) (
          0
         ))
        ))
       ))
      ))
     ) : (
                                          ((
       var_1_1
      ) == (
                                           ((unsigned char) (
        0
       ))
      ))
     ))
    ) && (
                                         ((
                                               ((
       var_1_4
      ) <= (
       var_1_5
      ))
     ) ? (
                                          ((
       var_1_8
      ) == (
                                           ((unsigned char) (
                                            ((
                                             ((((( var_1_9 )) < (( var_1_10 ))) ? (( var_1_9 )) : (( var_1_10 ))))
        ) - (
                                             ((
          64
         ) - (
          var_1_11
         ))
        ))
       ))
      ))
     ) : (
                                          ((
       var_1_8
      ) == (
                                           ((unsigned char) (
                                            ((((( ((((( var_1_9 )) < (( var_1_11 ))) ? (( var_1_9 )) : (( var_1_11 )))) )) > (( var_1_10 ))) ? (( ((((( var_1_9 )) < (( var_1_11 ))) ? (( var_1_9 )) : (( var_1_11 )))) )) : (( var_1_10 ))))
       ))
      ))
     ))
    ))
   ) && (
                                         ((
                                                ((
                                                 ((
                                                  ((
        var_1_10
       ) | (
        var_1_4
       ))
      ) * (
       var_1_8
      ))
     ) <= (
      var_1_5
     ))
    ) ? (
                                          ((
      var_1_12
     ) == (
                                           ((double) (
                                            ((
        var_1_13
       ) - (
        var_1_14
       ))
      ))
     ))
    ) : (
                                          ((
      var_1_12
     ) == (
                                           ((double) (
                                            ((
        var_1_15
       ) + (
        var_1_16
       ))
      ))
     ))
    ))
   ))
  ) && (
                                        ((
                                               ((
     var_1_14
    ) <= (
                                                ((((( var_1_13 )) > (( (( var_1_18 ) - ( var_1_19 )) ))) ? (( var_1_13 )) : (( (( var_1_18 ) - ( var_1_19 )) ))))
    ))
   ) ? (
                                         ((
     var_1_17
    ) == (
                                          ((unsigned char) (
      var_1_6
     ))
    ))
   ) : (
    1
   ))
  ))
 ) && (
                                       ((
                                              ((
    var_1_7
   ) || (
                                               ((
     var_1_17
    ) || (
     var_1_6
    ))
   ))
  ) ? (
                                        ((
    var_1_1
   ) ? (
                                         ((
     var_1_20
    ) == (
                                          ((float) (
                                           ((((( var_1_15 )) < (( ((((var_1_16) < 0 ) ? -(var_1_16) : (var_1_16))) ))) ? (( var_1_15 )) : (( ((((var_1_16) < 0 ) ? -(var_1_16) : (var_1_16))) ))))
     ))
    ))
   ) : (
    1
   ))
  ) : (
                                        ((
    var_1_20
   ) == (
                                         ((float) (
                                          ((
      var_1_16
     ) + (
      var_1_15
     ))
    ))
   ))
  ))
 ))
) && (
                                      ((
                                             (! (
   var_1_1
  ))
 ) ? (
                                       ((
   var_1_22
  ) == (
                                        ((unsigned short int) (
                                         ((((((((( var_1_8 )) < (( var_1_2 ))) ? (( var_1_8 )) : (( var_1_2 ))))) < 0 ) ? -(((((( var_1_8 )) < (( var_1_2 ))) ? (( var_1_8 )) : (( var_1_2 ))))) : (((((( var_1_8 )) < (( var_1_2 ))) ? (( var_1_8 )) : (( var_1_2 )))))))
   ))
  ))
 ) : (
                                       ((
                                              ((
    1
   ) < (
                                               ((
     var_1_3
    ) + (
     var_1_5
    ))
   ))
  ) ? (
                                        ((
    var_1_22
   ) == (
                                         ((unsigned short int) (
     var_1_9
    ))
   ))
  ) : (
                                        ((
    var_1_22
   ) == (
                                         ((unsigned short int) (
     var_1_8
    ))
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
