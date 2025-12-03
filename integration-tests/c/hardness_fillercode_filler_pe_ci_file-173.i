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
void reach_error(void) { __assert_fail("0", "Req1_Prop1_Batch173Filler_PE_CI.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
void initially(void);
void step(void);
void updateVariables(void);
void updateLastVariables(void);
int property(void);
int main(void);
unsigned char isInitial = 0;
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
unsigned char last_1_var_1_20 = 1;
void initially(void) {
}
void step(void) {
                                           if ( (( ((var_1_18) - (var_1_12))) >= ( (~ (var_1_14))))) {
                                            if (last_1_var_1_20) {
                                             var_1_17 = (
                                              ((((( (( var_1_19 ) - ( var_1_14 )) )) > (( var_1_12 ))) ? (( (( var_1_19 ) - ( var_1_14 )) )) : (( var_1_12 ))))
   );
  } else {
                                             var_1_17 = (
    var_1_12
   );
  }
 } else {
                                            var_1_17 = (
   var_1_14
  );
 }
 unsigned char stepLocal_2 = var_1_13;
 unsigned char stepLocal_1 = (( (((((var_1_4)) > ((var_1_3))) ? ((var_1_4)) : ((var_1_3))))) >= (var_1_5));
                                if ( ((stepLocal_1) || (var_1_9))) {
                                 if ( ((var_1_17) > (stepLocal_2))) {
                                  if (var_1_9) {
                                   var_1_20 = (
     var_1_21
    );
   } else {
                                   var_1_20 = (
     0
    );
   }
  } else {
                                  var_1_20 = (
    0
   );
  }
 } else {
                                 var_1_20 = (
   var_1_22
  );
 }
                               if ( ((var_1_13) > (2))) {
                                if (var_1_20) {
                                var_1_15 = (
                                 ((((( ((((var_1_13) < 0 ) ? -(var_1_13) : (var_1_13))) )) > (( (( 2813524572u ) - ( var_1_17 )) ))) ? (( ((((var_1_13) < 0 ) ? -(var_1_13) : (var_1_13))) )) : (( (( 2813524572u ) - ( var_1_17 )) ))))
   );
  } else {
                                 var_1_15 = (
                                  ((((( var_1_17 )) < (( var_1_14 ))) ? (( var_1_17 )) : (( var_1_14 ))))
   );
  }
 } else {
                                var_1_15 = (
                                 ((
    var_1_17
   ) + (
    100u
   ))
  );
 }
                               if ( ((var_1_11) <= (-128))) {
                                if ( ((var_1_6) <= (var_1_7))) {
                                  var_1_16 = (
    var_1_5
   );
  }
 }
                              if ( (! ( ((100u) >= (var_1_15))))) {
                               var_1_1 = (
                                ((((( var_1_3 )) > (( var_1_4 ))) ? (( var_1_3 )) : (( var_1_4 ))))
  );
 } else {
                               var_1_1 = (
                                ((
                                 ((
     var_1_5
    ) - (
     var_1_6
    ))
   ) + (
    var_1_7
   ))
  );
 }
 unsigned long int stepLocal_0 = var_1_15;
                              if (var_1_20) {
                               if ( (( ((var_1_15) / (var_1_11))) != (stepLocal_0))) {
                                var_1_8 = (
                                 ((
                                  ((
      var_1_12
     ) + (
      var_1_13
     ))
    ) + (
     var_1_14
    ))
   );
  } else {
                                var_1_8 = (
    var_1_14
   );
  }
 } else {
                               var_1_8 = (
   var_1_12
  );
 }
                  var_1_23 = (
  var_1_24
 );
                  if ( (( (( ((25) * (var_1_17))) ^ (var_1_17))) > (var_1_11))) {
                   var_1_25 = (
   var_1_24
  );
 }
                   if ( ((var_1_24) > (var_1_23))) {
                    var_1_29 = (
                     ((((((((var_1_15) < 0 ) ? -(var_1_15) : (var_1_15)))) < 0 ) ? -(((((var_1_15) < 0 ) ? -(var_1_15) : (var_1_15)))) : (((((var_1_15) < 0 ) ? -(var_1_15) : (var_1_15))))))
  );
 }
                   if ( ((var_1_24) < ( ((((var_1_25) < 0 ) ? -(var_1_25) : (var_1_25)))))) {
                    var_1_30 = (
                     ((
                      ((
                       ((((var_1_31) < 0 ) ? -(var_1_31) : (var_1_31)))
    ) + (
     256u
    ))
   ) + (
                      ((((( ((((( var_1_32 )) > (( var_1_33 ))) ? (( var_1_32 )) : (( var_1_33 )))) )) < (( var_1_34 ))) ? (( ((((( var_1_32 )) > (( var_1_33 ))) ? (( var_1_32 )) : (( var_1_33 )))) )) : (( var_1_34 ))))
   ))
  );
 }
                   if ( (( (( (((((var_1_14)) > ((var_1_13))) ? ((var_1_14)) : ((var_1_13))))) >> ( ((((var_1_38) < 0 ) ? -(var_1_38) : (var_1_38)))))) > (var_1_32))) {
                    var_1_35 = (
                     ((
                      ((
     var_1_20
    ) && (
     var_1_40
    ))
   ) || (
    var_1_41
   ))
  );
 } else {
                    var_1_35 = (
                     ((
    var_1_41
   ) || (
    var_1_40
   ))
  );
 }
                   if ( (( (((((var_1_34)) > (( ((((var_1_13) < 0 ) ? -(var_1_13) : (var_1_13)))))) ? ((var_1_34)) : (( ((((var_1_13) < 0 ) ? -(var_1_13) : (var_1_13)))))))) == (32u))) {
                    var_1_42 = (
   var_1_24
  );
 } else {
                    if ( ((var_1_15) < ( (~ (var_1_43))))) {
                     var_1_42 = (
                      (((((( (( var_1_44 ) + ( var_1_45 )) ) - ( var_1_46 ))) < 0 ) ? -((( (( var_1_44 ) + ( var_1_45 )) ) - ( var_1_46 ))) : ((( (( var_1_44 ) + ( var_1_45 )) ) - ( var_1_46 )))))
   );
  }
 }
                   if ( (( ((var_1_19) - (var_1_13))) > ( (((((var_1_15)) < ((var_1_13))) ? ((var_1_15)) : ((var_1_13))))))) {
                    if ( ((var_1_13) >= (5))) {
                     var_1_47 = (
    var_1_13
   );
  } else {
                     var_1_47 = (
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
 if ( (! ( ((100u) >= (var_1_15))))) {
 } else {
 }
 if (var_1_20) {
  if ( (( ((var_1_15) / (var_1_11))) != (var_1_15))) {
  } else {
  }
 } else {
 }
 if ( ((var_1_13) > (2))) {
  if (var_1_20) {
  } else {
  }
 } else {
 }
 if ( ((var_1_11) <= (-128))) {
  if ( ((var_1_6) <= (var_1_7))) {
  }
 }
 if ( (( ((var_1_18) - (var_1_12))) >= ( (~ (var_1_14))))) {
  if (last_1_var_1_20) {
  } else {
  }
 } else {
 }
 if ( (( (( (((((var_1_4)) > ((var_1_3))) ? ((var_1_4)) : ((var_1_3))))) >= (var_1_5))) || (var_1_9))) {
  if ( ((var_1_17) > (var_1_13))) {
   if (var_1_9) {
   } else {
   }
  } else {
  }
 } else {
 }
 return ((
             ((
              ((
               ((
                ((
                                         ((
                                              (! (
                                               ((
        100u
       ) >= (
        var_1_15
       ))
      ))
     ) ? (
                                          ((
       var_1_1
      ) == (
                                           ((float) (
                                            ((((( var_1_3 )) > (( var_1_4 ))) ? (( var_1_3 )) : (( var_1_4 ))))
       ))
      ))
     ) : (
                                          ((
       var_1_1
      ) == (
                                           ((float) (
                                            ((
                                             ((
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
                                         ((
      var_1_20
     ) ? (
                                          ((
                                                ((
                                                 ((
         var_1_15
        ) / (
         var_1_11
        ))
       ) != (
        var_1_15
       ))
      ) ? (
                                           ((
        var_1_8
       ) == (
                                            ((unsigned char) (
                                             ((
                                              ((
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
                                           ((
        var_1_8
       ) == (
                                            ((unsigned char) (
         var_1_14
        ))
       ))
      ))
     ) : (
                                          ((
       var_1_8
      ) == (
                                           ((unsigned char) (
        var_1_12
       ))
      ))
     ))
    ))
   ) && (
                                         ((
                                              ((
      var_1_13
     ) > (
      2
     ))
    ) ? (
                                          ((
      var_1_20
     ) ? (
                                          ((
       var_1_15
      ) == (
                                           ((unsigned long int) (
                                            ((((( ((((var_1_13) < 0 ) ? -(var_1_13) : (var_1_13))) )) > (( (( 2813524572u ) - ( var_1_17 )) ))) ? (( ((((var_1_13) < 0 ) ? -(var_1_13) : (var_1_13))) )) : (( (( 2813524572u ) - ( var_1_17 )) ))))
       ))
      ))
     ) : (
                                           ((
       var_1_15
      ) == (
                                            ((unsigned long int) (
                                             ((((( var_1_17 )) < (( var_1_14 ))) ? (( var_1_17 )) : (( var_1_14 ))))
       ))
      ))
     ))
    ) : (
                                          ((
      var_1_15
     ) == (
                                           ((unsigned long int) (
                                            ((
        var_1_17
       ) + (
        100u
       ))
      ))
     ))
    ))
   ))
  ) && (
                                        ((
                                               ((
     var_1_11
    ) <= (
     -128
    ))
   ) ? (
                                         ((
                                                ((
      var_1_6
     ) <= (
      var_1_7
     ))
    ) ? (
                                          ((
      var_1_16
     ) == (
                                           ((float) (
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
                                                  ((
                                                         ((
                                                          ((
     var_1_18
    ) - (
     var_1_12
    ))
   ) >= (
                                                          (~ (
     var_1_14
    ))
   ))
  ) ? (
                                                   ((
    last_1_var_1_20
   ) ? (
                                                    ((
     var_1_17
    ) == (
                                                     ((unsigned char) (
                                                      ((((( (( var_1_19 ) - ( var_1_14 )) )) > (( var_1_12 ))) ? (( (( var_1_19 ) - ( var_1_14 )) )) : (( var_1_12 ))))
     ))
    ))
   ) : (
                                                    ((
     var_1_17
    ) == (
                                                     ((unsigned char) (
      var_1_12
     ))
    ))
   ))
  ) : (
                                                   ((
    var_1_17
   ) == (
                                                    ((unsigned char) (
     var_1_14
    ))
   ))
  ))
 ))
) && (
                                      ((
                                             ((
                                              ((
                                               ((((( var_1_4 )) > (( var_1_3 ))) ? (( var_1_4 )) : (( var_1_3 ))))
   ) >= (
    var_1_5
   ))
  ) || (
   var_1_9
  ))
 ) ? (
                                       ((
                                              ((
    var_1_17
   ) > (
    var_1_13
   ))
  ) ? (
                                        ((
    var_1_9
   ) ? (
                                         ((
     var_1_20
    ) == (
                                          ((unsigned char) (
      var_1_21
     ))
    ))
   ) : (
                                         ((
     var_1_20
    ) == (
                                          ((unsigned char) (
      0
     ))
    ))
   ))
  ) : (
                                        ((
    var_1_20
   ) == (
                                         ((unsigned char) (
     0
    ))
   ))
  ))
 ) : (
                                       ((
   var_1_20
  ) == (
                                        ((unsigned char) (
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
