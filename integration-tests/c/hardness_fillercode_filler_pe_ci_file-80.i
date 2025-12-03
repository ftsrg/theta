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
void reach_error(void) { __assert_fail("0", "Req1_Prop1_Batch80Filler_PE_CI.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
void initially(void);
void step(void);
void updateVariables(void);
void updateLastVariables(void);
int property(void);
int main(void);
unsigned char isInitial = 0;
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
double last_1_var_1_19 = 4.9;
double last_1_var_1_24 = 1.8;
void initially(void) {
}
void step(void) {
                                         if ( (( (( ((var_1_2) - (var_1_3))) * (last_1_var_1_24))) < (last_1_var_1_24))) {
                                          var_1_1 = (
                                           ((((( -8 )) < (( (( var_1_6 ) + ( ((((( var_1_7 )) < (( var_1_8 ))) ? (( var_1_7 )) : (( var_1_8 )))) )) ))) ? (( -8 )) : (( (( var_1_6 ) + ( ((((( var_1_7 )) < (( var_1_8 ))) ? (( var_1_7 )) : (( var_1_8 )))) )) ))))
  );
 } else {
                                          var_1_1 = (
   var_1_6
  );
 }
                                if ( (( ((32) + (var_1_12))) != (var_1_1))) {
                                 var_1_24 = (
   var_1_21
  );
 }
                                          if (var_1_11) {
                                         var_1_10 = (
                                          ((((( 0 )) < (( var_1_12 ))) ? (( 0 )) : (( var_1_12 ))))
  );
 } else {
                                           if ( (! ( ((last_1_var_1_19) > ( ((255.9) / (var_1_13))))))) {
                                            var_1_10 = (
    var_1_12
   );
  }
 }
                               if ( (! (var_1_11))) {
                                if ( (( (( ((var_1_15) - (var_1_16))) - (var_1_17))) <= (var_1_13))) {
                                 var_1_14 = (
    var_1_10
   );
  } else {
                                 var_1_14 = (
    128
   );
  }
 }
                                if ( ((var_1_12) < ( ((1) + (var_1_14))))) {
                                 var_1_19 = (
                                  ((
    var_1_20
   ) + (
                                   ((((( (( 199.5 ) + ( var_1_21 )) )) > (( ((((( var_1_22 )) > (( var_1_23 ))) ? (( var_1_22 )) : (( var_1_23 )))) ))) ? (( (( 199.5 ) + ( var_1_21 )) )) : (( ((((( var_1_22 )) > (( var_1_23 ))) ? (( var_1_22 )) : (( var_1_23 )))) ))))
   ))
  );
 } else {
                                 var_1_19 = (
                                  ((
    var_1_22
   ) + (
    var_1_20
   ))
  );
 }
 signed short int stepLocal_0 = var_1_8;
                              if ( ((stepLocal_0) >= (var_1_7))) {
                               var_1_9 = (
                                ((
    -256
   ) + (
    var_1_6
   ))
  );
 } else {
                               var_1_9 = (
                                ((
    var_1_7
   ) + (
    var_1_6
   ))
  );
 }
                                if ( (( ((2935136887u) - ( ((var_1_12) + (var_1_10))))) <= (var_1_14))) {
                                 var_1_18 = (
   32
  );
 }
                   if ( (( ((var_1_26) & (var_1_27))) >= (-2))) {
                    var_1_25 = (
   var_1_21
  );
 }
                   var_1_29 = (
                    ((
                     ((
    8.18603254193775E18
   ) - (
                      ((
     var_1_30
    ) - (
     var_1_31
    ))
   ))
  ) - (
   var_1_32
  ))
 );
                   if (var_1_11) {
                    var_1_33 = (
                     ((
                      ((
     var_1_35
    ) + (
                       ((((( var_1_36 )) < (( var_1_37 ))) ? (( var_1_36 )) : (( var_1_37 ))))
    ))
   ) - (
                      ((
                       ((
      var_1_26
     ) + (
      var_1_27
     ))
    ) + (
                       ((((( 1000000000u )) < (( var_1_38 ))) ? (( 1000000000u )) : (( var_1_38 ))))
    ))
   ))
  );
 }
                   if ( (( ((var_1_33) | (var_1_38))) > (var_1_14))) {
                    if ( ((var_1_21) <= ( ((((var_1_24) < 0 ) ? -(var_1_24) : (var_1_24)))))) {
                     var_1_39 = (
                      ((((( var_1_36 )) < (( (( ((((var_1_40) < 0 ) ? -(var_1_40) : (var_1_40))) ) - ( var_1_14 )) ))) ? (( var_1_36 )) : (( (( ((((var_1_40) < 0 ) ? -(var_1_40) : (var_1_40))) ) - ( var_1_14 )) ))))
   );
  } else {
                     if ( ((var_1_14) > ( ((((var_1_33) < 0 ) ? -(var_1_33) : (var_1_33)))))) {
                      var_1_39 = (
     var_1_38
    );
   } else {
                      var_1_39 = (
                       ((((var_1_14) < 0 ) ? -(var_1_14) : (var_1_14)))
    );
   }
  }
 }
                   if ( (( ((((( ((var_1_30) * (var_1_32)))) < ((var_1_19))) ? (( ((var_1_30) * (var_1_32)))) : ((var_1_19))))) >= ( (- (var_1_20))))) {
                    if ( ((var_1_35) > (var_1_40))) {
                     var_1_41 = (
                      ((
     8
    ) + (
                       ((((( var_1_42 )) < (( var_1_43 ))) ? (( var_1_42 )) : (( var_1_43 ))))
    ))
   );
  } else {
                     var_1_41 = (
    var_1_44
   );
  }
 }
                   if ( ((-32) < ( ((var_1_42) & (var_1_14))))) {
                    var_1_45 = (
                     ((((( var_1_12 )) < (( (( var_1_47 ) + ( 10 )) ))) ? (( var_1_12 )) : (( (( var_1_47 ) + ( 10 )) ))))
  );
 } else {
                    var_1_45 = (
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
 if ( (( (( ((var_1_2) - (var_1_3))) * (last_1_var_1_24))) < (last_1_var_1_24))) {
 } else {
 }
 if ( ((var_1_8) >= (var_1_7))) {
 } else {
 }
 if (var_1_11) {
 } else {
  if ( (! ( ((last_1_var_1_19) > ( ((255.9) / (var_1_13))))))) {
  }
 }
 if ( (! (var_1_11))) {
  if ( (( (( ((var_1_15) - (var_1_16))) - (var_1_17))) <= (var_1_13))) {
  } else {
  }
 }
 if ( (( ((2935136887u) - ( ((var_1_12) + (var_1_10))))) <= (var_1_14))) {
 }
 if ( ((var_1_12) < ( ((1) + (var_1_14))))) {
 } else {
 }
 if ( (( ((32) + (var_1_12))) != (var_1_1))) {
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
                                                            ((
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
                                                      ((
        var_1_1
       ) == (
                                                       ((signed short int) (
                                                        ((((( -8 )) < (( (( var_1_6 ) + ( ((((( var_1_7 )) < (( var_1_8 ))) ? (( var_1_7 )) : (( var_1_8 )))) )) ))) ? (( -8 )) : (( (( var_1_6 ) + ( ((((( var_1_7 )) < (( var_1_8 ))) ? (( var_1_7 )) : (( var_1_8 )))) )) ))))
        ))
       ))
      ) : (
                                                      ((
        var_1_1
       ) == (
                                                       ((signed short int) (
         var_1_6
        ))
       ))
      ))
     ) && (
                                          ((
                                                ((
        var_1_8
       ) >= (
        var_1_7
       ))
      ) ? (
                                           ((
        var_1_9
       ) == (
                                            ((signed short int) (
                                             ((
          -256
         ) + (
          var_1_6
         ))
        ))
       ))
      ) : (
                                           ((
        var_1_9
       ) == (
                                            ((signed short int) (
                                             ((
          var_1_7
         ) + (
          var_1_6
         ))
        ))
       ))
      ))
     ))
    ) && (
                                                     ((
      var_1_11
     ) ? (
                                                     ((
       var_1_10
      ) == (
                                                      ((unsigned char) (
                                                       ((((( 0 )) < (( var_1_12 ))) ? (( 0 )) : (( var_1_12 ))))
       ))
      ))
     ) : (
                                                      ((
                                                           (! (
                                                            ((
         last_1_var_1_19
        ) > (
                                                             ((
          255.9
         ) / (
          var_1_13
         ))
        ))
       ))
      ) ? (
                                                       ((
        var_1_10
       ) == (
                                                        ((unsigned char) (
         var_1_12
        ))
       ))
      ) : (
       1
      ))
     ))
    ))
   ) && (
                                         ((
                                                (! (
      var_1_11
     ))
    ) ? (
                                          ((
                                                 ((
                                                  ((
                                                   ((
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
                                           ((
       var_1_14
      ) == (
                                            ((unsigned short int) (
        var_1_10
       ))
      ))
     ) : (
                                           ((
       var_1_14
      ) == (
                                            ((unsigned short int) (
        128
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
      2935136887u
     ) - (
                                                 ((
       var_1_12
      ) + (
       var_1_10
      ))
     ))
    ) <= (
     var_1_14
    ))
   ) ? (
                                         ((
     var_1_18
    ) == (
                                          ((signed char) (
      32
     ))
    ))
   ) : (
    1
   ))
  ))
 ) && (
                                       ((
                                              ((
    var_1_12
   ) < (
                                               ((
     1
    ) + (
     var_1_14
    ))
   ))
  ) ? (
                                        ((
    var_1_19
   ) == (
                                         ((double) (
                                          ((
      var_1_20
     ) + (
                                           ((((( (( 199.5 ) + ( var_1_21 )) )) > (( ((((( var_1_22 )) > (( var_1_23 ))) ? (( var_1_22 )) : (( var_1_23 )))) ))) ? (( (( 199.5 ) + ( var_1_21 )) )) : (( ((((( var_1_22 )) > (( var_1_23 ))) ? (( var_1_22 )) : (( var_1_23 )))) ))))
     ))
    ))
   ))
  ) : (
                                        ((
    var_1_19
   ) == (
                                         ((double) (
                                          ((
      var_1_22
     ) + (
      var_1_20
     ))
    ))
   ))
  ))
 ))
) && (
                                      ((
                                             ((
                                              ((
    32
   ) + (
    var_1_12
   ))
  ) != (
   var_1_1
  ))
 ) ? (
                                       ((
   var_1_24
  ) == (
                                        ((double) (
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
