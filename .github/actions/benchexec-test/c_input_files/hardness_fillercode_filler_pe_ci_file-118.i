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
void reach_error(void) { __assert_fail("0", "Req1_Prop1_Batch118Filler_PE_CI.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
void initially(void);
void step(void);
void updateVariables(void);
void updateLastVariables(void);
int property(void);
int main(void);
unsigned char isInitial = 0;
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
void initially(void) {
}
void step(void) {
                              var_1_1 = (
  -5
 );
                               var_1_2 = (
                                ((((( var_1_3 )) > (( var_1_4 ))) ? (( var_1_3 )) : (( var_1_4 ))))
 );
                                if ( ((var_1_8) && (var_1_9))) {
                                 var_1_7 = (
   var_1_6
  );
 }
 unsigned char stepLocal_1 = ((var_1_8) || (var_1_15));
                                if ( ((var_1_9) && (stepLocal_1))) {
                                 var_1_14 = (
                                  ((
                                   ((
                                    ((
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
                                 var_1_14 = (
                                  ((
    var_1_13
   ) + (
    var_1_17
   ))
  );
 }
                                if (var_1_8) {
                                 if (var_1_15) {
                                  var_1_18 = (
                                   ((
                                    ((
                                     ((((var_1_4) < 0 ) ? -(var_1_4) : (var_1_4)))
     ) + (
      var_1_2
     ))
    ) + (
     var_1_3
    ))
   );
  } else {
                                  var_1_18 = (
    var_1_2
   );
  }
 }
                                if ( (( (( ((var_1_18) + (var_1_1))) & (var_1_3))) >= (var_1_4))) {
                                 var_1_19 = (
   10000.5
  );
 } else {
                                 var_1_19 = (
   var_1_6
  );
 }
                                if ( ((-2) < ( ((var_1_3) + (var_1_18))))) {
                                 if ( (( ((var_1_3) * (var_1_18))) >= (var_1_2))) {
                                 var_1_5 = (
    var_1_6
   );
  } else {
                                  var_1_5 = (
    49.25f
   );
  }
 } else {
                                 var_1_5 = (
   var_1_6
  );
 }
 unsigned char stepLocal_0 = (( ((var_1_18) - (var_1_3))) > ( ((var_1_4) + (var_1_1))));
                                if ( ((stepLocal_0) && ( ((var_1_19) > (var_1_6))))) {
                                 var_1_10 = (
   var_1_6
  );
 } else {
                                 var_1_10 = (
   9.25
  );
 }
                                if ( ((var_1_14) == (var_1_6))) {
                                 var_1_11 = (
                                  ((
    32.7f
   ) + (
                                   ((
     var_1_12
    ) - (
     var_1_13
    ))
   ))
  );
 }
                  if (var_1_9) {
                   if ( (! (var_1_9))) {
                    var_1_20 = (
    var_1_23
   );
  }
 }
                  var_1_24 = (
  var_1_23
 );
                  var_1_25 = (
  var_1_20
 );
                  if ( ((var_1_25) > ( ((((var_1_23) < 0 ) ? -(var_1_23) : (var_1_23)))))) {
                   if ( ((var_1_25) == ( ((var_1_20) & (var_1_24))))) {
                    var_1_26 = (
    var_1_27
   );
  }
 } else {
                   var_1_26 = (
   var_1_27
  );
 }
                   if ( ((var_1_25) > (var_1_20))) {
                    if ( ((var_1_25) > ( (((((var_1_20)) > ((var_1_24))) ? ((var_1_20)) : ((var_1_24))))))) {
                     var_1_28 = (
                      ((
     var_1_17
    ) + (
     4.3f
    ))
   );
  } else {
                     var_1_28 = (
                      ((((( ((((( var_1_17 )) > (( var_1_6 ))) ? (( var_1_17 )) : (( var_1_6 )))) )) < (( var_1_6 ))) ? (( ((((( var_1_17 )) > (( var_1_6 ))) ? (( var_1_17 )) : (( var_1_6 )))) )) : (( var_1_6 ))))
   );
  }
 } else {
                    var_1_28 = (
                     ((
    var_1_32
   ) - (
                      ((((( ((((( 32.8f )) > (( var_1_33 ))) ? (( 32.8f )) : (( var_1_33 )))) )) < (( var_1_34 ))) ? (( ((((( 32.8f )) > (( var_1_33 ))) ? (( 32.8f )) : (( var_1_33 )))) )) : (( var_1_34 ))))
   ))
  );
 }
                   if ( ((var_1_13) != ( ((((var_1_13) < 0 ) ? -(var_1_13) : (var_1_13)))))) {
                    var_1_35 = (
   var_1_24
  );
 } else {
                    var_1_35 = (
                     ((
                      ((((( ((((var_1_20) < 0 ) ? -(var_1_20) : (var_1_20))) )) < (( ((((( var_1_24 )) > (( var_1_23 ))) ? (( var_1_24 )) : (( var_1_23 )))) ))) ? (( ((((var_1_20) < 0 ) ? -(var_1_20) : (var_1_20))) )) : (( ((((( var_1_24 )) > (( var_1_23 ))) ? (( var_1_24 )) : (( var_1_23 )))) ))))
   ) + (
                      ((
                       ((((var_1_36) < 0 ) ? -(var_1_36) : (var_1_36)))
    ) - (
                       ((((var_1_37) < 0 ) ? -(var_1_37) : (var_1_37)))
    ))
   ))
  );
 }
                   if ( (( ((var_1_37) >> ( ((var_1_39) - (var_1_40))))) <= (var_1_23))) {
                    var_1_38 = (
   var_1_23
  );
 }
                   if ( ((var_1_24) != (var_1_37))) {
                    if ( (! (var_1_8))) {
                     var_1_41 = (
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
 if ( ((-2) < ( ((var_1_3) + (var_1_18))))) {
  if ( (( ((var_1_3) * (var_1_18))) >= (var_1_2))) {
  } else {
  }
 } else {
 }
 if ( ((var_1_8) && (var_1_9))) {
 }
 if ( (( (( ((var_1_18) - (var_1_3))) > ( ((var_1_4) + (var_1_1))))) && ( ((var_1_19) > (var_1_6))))) {
 } else {
 }
 if ( ((var_1_14) == (var_1_6))) {
 }
 if ( ((var_1_9) && ( ((var_1_8) || (var_1_15))))) {
 } else {
 }
 if (var_1_8) {
  if (var_1_15) {
  } else {
  }
 }
 if ( (( (( ((var_1_18) + (var_1_1))) & (var_1_3))) >= (var_1_4))) {
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
                                           ((
         var_1_1
        ) == (
                                            ((signed short int) (
          -5
         ))
        ))
       ) && (
                                            ((
         var_1_2
        ) == (
                                             ((unsigned char) (
                                              ((((( var_1_3 )) > (( var_1_4 ))) ? (( var_1_3 )) : (( var_1_4 ))))
         ))
        ))
       ))
      ) && (
                                            ((
                                                 ((
         -2
        ) < (
                                                  ((
          var_1_3
         ) + (
          var_1_18
         ))
        ))
       ) ? (
                                             ((
                                                  ((
                                                   ((
           var_1_3
          ) * (
           var_1_18
          ))
         ) >= (
          var_1_2
         ))
        ) ? (
                                             ((
          var_1_5
         ) == (
                                              ((float) (
           var_1_6
          ))
         ))
        ) : (
                                              ((
          var_1_5
         ) == (
                                               ((float) (
           49.25f
          ))
         ))
        ))
       ) : (
                                             ((
         var_1_5
        ) == (
                                              ((float) (
          var_1_6
         ))
        ))
       ))
      ))
     ) && (
                                           ((
                                                  ((
        var_1_8
       ) && (
        var_1_9
       ))
      ) ? (
                                            ((
        var_1_7
       ) == (
                                             ((double) (
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
                                                  ((
                                                   ((
         var_1_18
        ) - (
         var_1_3
        ))
       ) > (
                                                   ((
         var_1_4
        ) + (
         var_1_1
        ))
       ))
      ) && (
                                                  ((
        var_1_19
       ) > (
        var_1_6
       ))
      ))
     ) ? (
                                           ((
       var_1_10
      ) == (
                                            ((double) (
        var_1_6
       ))
      ))
     ) : (
                                           ((
       var_1_10
      ) == (
                                            ((double) (
        9.25
       ))
      ))
     ))
    ))
   ) && (
                                         ((
                                                ((
      var_1_14
     ) == (
      var_1_6
     ))
    ) ? (
                                          ((
      var_1_11
     ) == (
                                           ((float) (
                                            ((
        32.7f
       ) + (
                                             ((
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
                                        ((
                                               ((
     var_1_9
    ) && (
                                                ((
      var_1_8
     ) || (
      var_1_15
     ))
    ))
   ) ? (
                                         ((
     var_1_14
    ) == (
                                          ((double) (
                                           ((
                                            ((
                                             ((
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
                                         ((
     var_1_14
    ) == (
                                          ((double) (
                                           ((
       var_1_13
      ) + (
       var_1_17
      ))
     ))
    ))
   ))
  ))
 ) && (
                                       ((
   var_1_8
  ) ? (
                                        ((
    var_1_15
   ) ? (
                                         ((
     var_1_18
    ) == (
                                          ((signed short int) (
                                           ((
                                            ((
                                             ((((var_1_4) < 0 ) ? -(var_1_4) : (var_1_4)))
       ) + (
        var_1_2
       ))
      ) + (
       var_1_3
      ))
     ))
    ))
   ) : (
                                         ((
     var_1_18
    ) == (
                                          ((signed short int) (
      var_1_2
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
                                               ((
                                                ((
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
                                        ((
   var_1_19
  ) == (
                                         ((double) (
    10000.5
   ))
  ))
 ) : (
                                         ((
   var_1_19
  ) == (
                                          ((double) (
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
