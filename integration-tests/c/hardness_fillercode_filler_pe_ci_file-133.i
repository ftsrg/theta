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
void reach_error(void) { __assert_fail("0", "Req1_Prop1_Batch133Filler_PE_CI.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
void initially(void);
void step(void);
void updateVariables(void);
void updateLastVariables(void);
int property(void);
int main(void);
unsigned char isInitial = 0;
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
void initially(void) {
}
void step(void) {
 unsigned char stepLocal_1 = (! (var_1_2));
 signed long int stepLocal_0 = var_1_5;
                               if ( ((stepLocal_1) || ( ((var_1_3) && (var_1_4))))) {
                                if ( ((stepLocal_0) == (var_1_6))) {
                                 var_1_1 = (
    var_1_7
   );
  } else {
                                 var_1_1 = (
    -128
   );
  }
 } else {
                                var_1_1 = (
   var_1_7
  );
 }
 signed short int stepLocal_2 = var_1_7;
                               if ( ((stepLocal_2) > ( ((var_1_9) - (var_1_10))))) {
                                var_1_8 = (
                                 ((((var_1_7) < 0 ) ? -(var_1_7) : (var_1_7)))
  );
 }
                               var_1_11 = (
                                ((((( var_1_10 )) < (( var_1_12 ))) ? (( var_1_10 )) : (( var_1_12 ))))
 );
                                if ( (( (((((var_1_18)) > ((var_1_19))) ? ((var_1_18)) : ((var_1_19))))) != ( ((var_1_20) * (9999.5))))) {
                                 var_1_17 = (
                                  ((
                                   ((
     var_1_21
    ) + (
     2
    ))
   ) + (
    -64
   ))
  );
 }
                                if ( (( ((var_1_7) / ( ((((var_1_23) < 0 ) ? -(var_1_23) : (var_1_23)))))) > ( ((25) - (var_1_10))))) {
                                 var_1_22 = (
   var_1_15
  );
 }
                                  var_1_24 = (
  var_1_25
 );
 unsigned long int stepLocal_4 = var_1_11;
 signed long int stepLocal_3 = -50;
                                if ( ((var_1_11) == (stepLocal_3))) {
                                 if ( ((stepLocal_4) > (10u))) {
                                  var_1_13 = (
                                   ((
     var_1_22
    ) && (
     var_1_14
    ))
   );
  } else {
                                  var_1_13 = (
    var_1_15
   );
  }
 } else {
                                 var_1_13 = (
   var_1_15
  );
 }
 unsigned long int stepLocal_5 = ((var_1_11) + ( ((var_1_11) * (10u))));
                                if ( ((var_1_12) != (stepLocal_5))) {
                                 var_1_16 = (
                                  ((
                                   ((
     var_1_9
    ) < (
     var_1_8
    ))
   ) && (
                                   (! (
     var_1_15
    ))
   ))
  );
 } else {
                                 if ( (! (var_1_22))) {
                                  var_1_16 = (
    0
   );
  } else {
                                  var_1_16 = (
    var_1_15
   );
  }
 }
                 var_1_26 = (
  var_1_27
 );
                  if ( (( (( ((var_1_23) & (var_1_5))) | (var_1_11))) >= (var_1_8))) {
                   var_1_28 = (
                    ((((var_1_12) < 0 ) ? -(var_1_12) : (var_1_12)))
  );
 }
                  var_1_34 = (
  var_1_7
 );
                  if (var_1_15) {
                   var_1_36 = (
                    ((((( ((((( ((((var_1_38) < 0 ) ? -(var_1_38) : (var_1_38))) )) < (( var_1_39 ))) ? (( ((((var_1_38) < 0 ) ? -(var_1_38) : (var_1_38))) )) : (( var_1_39 )))) )) < (( (((((( var_1_40 ) + ( var_1_41 ))) < 0 ) ? -((( var_1_40 ) + ( var_1_41 ))) : ((( var_1_40 ) + ( var_1_41 ))))) ))) ? (( ((((( ((((var_1_38) < 0 ) ? -(var_1_38) : (var_1_38))) )) < (( var_1_39 ))) ? (( ((((var_1_38) < 0 ) ? -(var_1_38) : (var_1_38))) )) : (( var_1_39 )))) )) : (( (((((( var_1_40 ) + ( var_1_41 ))) < 0 ) ? -((( var_1_40 ) + ( var_1_41 ))) : ((( var_1_40 ) + ( var_1_41 ))))) ))))
  );
 }
                  if ( ((var_1_6) > (-16))) {
                   var_1_42 = (
                    ((
                     ((((var_1_43) < 0 ) ? -(var_1_43) : (var_1_43)))
   ) - (
    var_1_40
   ))
  );
 } else {
                   var_1_42 = (
   var_1_43
  );
 }
                   if ( ((var_1_5) <= (var_1_39))) {
                    if ( (( (( ((var_1_23) + (var_1_12))) ^ ( ((var_1_5) / (var_1_45))))) <= (var_1_12))) {
                     var_1_44 = (
                      (((((( var_1_47 ) + ( var_1_48 ))) < 0 ) ? -((( var_1_47 ) + ( var_1_48 ))) : ((( var_1_47 ) + ( var_1_48 )))))
   );
  } else {
                     var_1_44 = (
                      ((
     var_1_49
    ) - (
     var_1_50
    ))
   );
  }
 } else {
                    var_1_44 = (
   var_1_50
  );
 }
                   var_1_51 = (
                    ((
   var_1_52
  ) - (
                     ((
    var_1_53
   ) + (
                      ((
     var_1_54
    ) + (
     var_1_55
    ))
   ))
  ))
 );
                   if ( ((var_1_7) == ( (((((-10000)) > ((var_1_11))) ? ((-10000)) : ((var_1_11))))))) {
                    var_1_56 = (
                     ((
                      ((
     var_1_49
    ) <= (
                       ((
      var_1_5
     ) * (
      var_1_12
     ))
    ))
   ) || (
                      ((
     var_1_57
    ) && (
     var_1_58
    ))
   ))
  );
 } else {
                    if ( (( (((((var_1_27)) < ((25.5f))) ? ((var_1_27)) : ((25.5f))))) > (128.25))) {
                     var_1_56 = (
    var_1_59
   );
  } else {
                     var_1_56 = (
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
 if ( (( (! (var_1_2))) || ( ((var_1_3) && (var_1_4))))) {
  if ( ((var_1_5) == (var_1_6))) {
  } else {
  }
 } else {
 }
 if ( ((var_1_7) > ( ((var_1_9) - (var_1_10))))) {
 }
 if ( ((var_1_11) == (-50))) {
  if ( ((var_1_11) > (10u))) {
  } else {
  }
 } else {
 }
 if ( ((var_1_12) != ( ((var_1_11) + ( ((var_1_11) * (10u))))))) {
 } else {
  if ( (! (var_1_22))) {
  } else {
  }
 }
 if ( (( (((((var_1_18)) > ((var_1_19))) ? ((var_1_18)) : ((var_1_19))))) != ( ((var_1_20) * (9999.5))))) {
 }
 if ( (( ((var_1_7) / ( ((((var_1_23) < 0 ) ? -(var_1_23) : (var_1_23)))))) > ( ((25) - (var_1_10))))) {
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
                                                 (! (
          var_1_2
         ))
        ) || (
                                                 ((
          var_1_3
         ) && (
          var_1_4
         ))
        ))
       ) ? (
                                            ((
                                                  ((
          var_1_5
         ) == (
          var_1_6
         ))
        ) ? (
                                             ((
          var_1_1
         ) == (
                                              ((signed short int) (
           var_1_7
          ))
         ))
        ) : (
                                             ((
          var_1_1
         ) == (
                                              ((signed short int) (
           -128
          ))
         ))
        ))
       ) : (
                                            ((
         var_1_1
        ) == (
                                             ((signed short int) (
          var_1_7
         ))
        ))
       ))
      ) && (
                                           ((
                                                 ((
         var_1_7
        ) > (
                                                  ((
          var_1_9
         ) - (
          var_1_10
         ))
        ))
       ) ? (
                                            ((
         var_1_8
        ) == (
                                             ((signed long int) (
                                              ((((var_1_7) < 0 ) ? -(var_1_7) : (var_1_7)))
         ))
        ))
       ) : (
        1
       ))
      ))
     ) && (
                                          ((
       var_1_11
      ) == (
                                           ((unsigned long int) (
                                            ((((( var_1_10 )) < (( var_1_12 ))) ? (( var_1_10 )) : (( var_1_12 ))))
       ))
      ))
     ))
    ) && (
                                          ((
                                                ((
       var_1_11
      ) == (
       -50
      ))
     ) ? (
                                           ((
                                                  ((
        var_1_11
       ) > (
        10u
       ))
      ) ? (
                                            ((
        var_1_13
       ) == (
                                             ((unsigned char) (
                                              ((
          var_1_22
         ) && (
          var_1_14
         ))
        ))
       ))
      ) : (
                                            ((
        var_1_13
       ) == (
                                             ((unsigned char) (
         var_1_15
        ))
       ))
      ))
     ) : (
                                           ((
       var_1_13
      ) == (
                                            ((unsigned char) (
        var_1_15
       ))
      ))
     ))
    ))
   ) && (
                                         ((
                                                ((
      var_1_12
     ) != (
                                                 ((
       var_1_11
      ) + (
                                                  ((
        var_1_11
       ) * (
        10u
       ))
      ))
     ))
    ) ? (
                                          ((
      var_1_16
     ) == (
                                           ((unsigned char) (
                                            ((
                                             ((
         var_1_9
        ) < (
         var_1_8
        ))
       ) && (
                                             (! (
         var_1_15
        ))
       ))
      ))
     ))
    ) : (
                                          ((
                                                 (! (
       var_1_22
      ))
     ) ? (
                                           ((
       var_1_16
      ) == (
                                            ((unsigned char) (
        0
       ))
      ))
     ) : (
                                           ((
       var_1_16
      ) == (
                                            ((unsigned char) (
        var_1_15
       ))
      ))
     ))
    ))
   ))
  ) && (
                                        ((
                                               ((
                                                ((((( var_1_18 )) > (( var_1_19 ))) ? (( var_1_18 )) : (( var_1_19 ))))
    ) != (
                                                ((
      var_1_20
     ) * (
      9999.5
     ))
    ))
   ) ? (
                                         ((
     var_1_17
    ) == (
                                          ((signed short int) (
                                           ((
                                            ((
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
                                        ((
                                               ((
                                                ((
     var_1_7
    ) / (
                                                 ((((var_1_23) < 0 ) ? -(var_1_23) : (var_1_23)))
    ))
   ) > (
                                                 ((
     25
    ) - (
     var_1_10
    ))
   ))
  ) ? (
                                          ((
    var_1_22
   ) == (
                                           ((unsigned char) (
     var_1_15
    ))
   ))
  ) : (
   1
  ))
 ))
) && (
                                        ((
  var_1_24
 ) == (
                                         ((signed char) (
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
