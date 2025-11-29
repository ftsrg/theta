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
void reach_error(void) { __assert_fail("0", "Req1_Prop1_Batch78Filler_PE_CO.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
void initially(void);
void step(void);
void updateVariables(void);
void updateLastVariables(void);
int property(void);
int main(void);
unsigned char isInitial = 0;
signed long int var_1_1 = -4;
signed long int var_1_2 = 0;
unsigned char var_1_3 = 64;
unsigned char var_1_4 = 0;
unsigned char var_1_5 = 2;
unsigned short int var_1_6 = 10;
unsigned short int var_1_7 = 8;
double var_1_8 = 1.875;
signed long int var_1_9 = -4;
double var_1_10 = 63.5;
double var_1_11 = 255.375;
double var_1_12 = 999999999.525;
double var_1_13 = 63.75;
double var_1_14 = 0.625;
unsigned short int var_1_15 = 5;
signed char var_1_16 = 4;
signed char var_1_17 = 0;
signed char var_1_18 = -2;
signed char var_1_19 = 1;
unsigned short int var_1_20 = 50;
unsigned short int var_1_21 = 0;
unsigned char var_1_22 = 2;
unsigned char var_1_23 = 32;
unsigned short int var_1_24 = 8;
unsigned short int var_1_26 = 26914;
unsigned short int var_1_27 = 26182;
unsigned char var_1_28 = 5;
unsigned char var_1_29 = 50;
unsigned char var_1_30 = 10;
signed long int var_1_31 = -32;
signed long int var_1_32 = 16;
signed char var_1_33 = -10;
signed char var_1_35 = 0;
signed char var_1_36 = -2;
signed char var_1_37 = -1;
signed char var_1_38 = 64;
signed char var_1_39 = 4;
float var_1_40 = 15.75;
float var_1_43 = 49.5;
float var_1_44 = 128.5;
float var_1_45 = 64.8;
float var_1_46 = 256.85;
float var_1_47 = 9.3;
unsigned char var_1_48 = 0;
unsigned char var_1_49 = 0;
double var_1_50 = 5.4;
signed long int last_1_var_1_1 = -4;
unsigned short int last_1_var_1_6 = 10;
unsigned short int last_1_var_1_21 = 0;
void initially(void) {
}
void step(void) {
                                          if ( (( ((((var_1_4) < 0 ) ? -(var_1_4) : (var_1_4)))) > (last_1_var_1_1))) {
                                           var_1_15 = (
                                            ((((( last_1_var_1_21 )) > (( (( var_1_5 ) + ( var_1_4 )) ))) ? (( last_1_var_1_21 )) : (( (( var_1_5 ) + ( var_1_4 )) ))))
  );
 }
                             var_1_1 = (
                              ((((var_1_2) < 0 ) ? -(var_1_2) : (var_1_2)))
 );
 signed long int stepLocal_0 = var_1_1;
                              if ( ((stepLocal_0) < (var_1_2))) {
                               var_1_3 = (
                                ((((( var_1_4 )) > (( var_1_5 ))) ? (( var_1_4 )) : (( var_1_5 ))))
  );
 }
 signed long int stepLocal_2 = -256;
 unsigned char stepLocal_1 = var_1_5;
                              if ( (( ((var_1_2) ^ (var_1_1))) < (stepLocal_2))) {
                               var_1_6 = (
                                ((((((((( ((((( var_1_5 )) > (( var_1_4 ))) ? (( var_1_5 )) : (( var_1_4 )))) )) > (( (( last_1_var_1_6 ) + ( var_1_7 )) ))) ? (( ((((( var_1_5 )) > (( var_1_4 ))) ? (( var_1_5 )) : (( var_1_4 )))) )) : (( (( last_1_var_1_6 ) + ( var_1_7 )) ))))) < 0 ) ? -(((((( ((((( var_1_5 )) > (( var_1_4 ))) ? (( var_1_5 )) : (( var_1_4 )))) )) > (( (( last_1_var_1_6 ) + ( var_1_7 )) ))) ? (( ((((( var_1_5 )) > (( var_1_4 ))) ? (( var_1_5 )) : (( var_1_4 )))) )) : (( (( last_1_var_1_6 ) + ( var_1_7 )) ))))) : (((((( ((((( var_1_5 )) > (( var_1_4 ))) ? (( var_1_5 )) : (( var_1_4 )))) )) > (( (( last_1_var_1_6 ) + ( var_1_7 )) ))) ? (( ((((( var_1_5 )) > (( var_1_4 ))) ? (( var_1_5 )) : (( var_1_4 )))) )) : (( (( last_1_var_1_6 ) + ( var_1_7 )) )))))))
  );
 } else {
                               if ( ((stepLocal_1) <= (50))) {
                                var_1_6 = (
    last_1_var_1_6
   );
  }
 }
                               if ( ((var_1_1) < ( ((var_1_5) % ( (((((32)) > ((var_1_9))) ? ((32)) : ((var_1_9))))))))) {
                                var_1_8 = (
                                 ((
                                  ((
                                   ((((( var_1_10 )) > (( var_1_11 ))) ? (( var_1_10 )) : (( var_1_11 ))))
    ) - (
     var_1_12
    ))
   ) + (
                                  ((
     var_1_13
    ) - (
     var_1_14
    ))
   ))
  );
 } else {
                                if ( ((var_1_13) <= ( ((var_1_14) + (var_1_11))))) {
                                 var_1_8 = (
    var_1_12
   );
  }
 }
                               var_1_16 = (
                                ((
   var_1_17
  ) + (
                                 ((
    var_1_18
   ) + (
                                  ((((var_1_19) < 0 ) ? -(var_1_19) : (var_1_19)))
   ))
  ))
 );
 signed long int stepLocal_3 = (( ((var_1_2) * (var_1_17))) & ( ((var_1_6) * (var_1_18))));
                               if ( ((var_1_15) == (stepLocal_3))) {
                                var_1_21 = (
                                 ((
    var_1_4
   ) + (
    128
   ))
  );
 }
                               var_1_20 = (
                                ((((( (( var_1_5 ) + ( var_1_21 )) )) > (( var_1_4 ))) ? (( (( var_1_5 ) + ( var_1_21 )) )) : (( var_1_4 ))))
 );
                  var_1_22 = (
  var_1_23
 );
                  if ( (( (((((var_1_15)) < ((var_1_23))) ? ((var_1_15)) : ((var_1_23))))) >= (var_1_1))) {
                   var_1_24 = (
                    ((
                     ((
     var_1_26
    ) + (
     var_1_27
    ))
   ) - (
    var_1_23
   ))
  );
 }
                  if ( ((var_1_27) > (0))) {
                   var_1_28 = (
                    ((((( ((((( (( var_1_29 ) + ( var_1_30 )) )) > (( var_1_23 ))) ? (( (( var_1_29 ) + ( var_1_30 )) )) : (( var_1_23 )))) )) < (( 0 ))) ? (( ((((( (( var_1_29 ) + ( var_1_30 )) )) > (( var_1_23 ))) ? (( (( var_1_29 ) + ( var_1_30 )) )) : (( var_1_23 )))) )) : (( 0 ))))
  );
 }
                   if ( ((var_1_26) != ( ((var_1_30) + (var_1_29))))) {
                    var_1_31 = (
                     (((((( var_1_29 ) + ( ((((32) < 0 ) ? -(32) : (32))) ))) < 0 ) ? -((( var_1_29 ) + ( ((((32) < 0 ) ? -(32) : (32))) ))) : ((( var_1_29 ) + ( ((((32) < 0 ) ? -(32) : (32))) )))))
  );
 }
                   if ( ((var_1_26) > (100))) {
                    if ( (( (( ((((var_1_27) < 0 ) ? -(var_1_27) : (var_1_27)))) ^ (var_1_26))) > (var_1_1))) {
                     var_1_32 = (
                      ((
     var_1_29
    ) - (
     var_1_26
    ))
   );
  } else {
                     var_1_32 = (
    var_1_21
   );
  }
 }
                   if ( ((var_1_1) < ( ((var_1_26) + (var_1_1))))) {
                    var_1_33 = (
                     ((((((((( var_1_35 )) < (( var_1_36 ))) ? (( var_1_35 )) : (( var_1_36 ))))) < 0 ) ? -(((((( var_1_35 )) < (( var_1_36 ))) ? (( var_1_35 )) : (( var_1_36 ))))) : (((((( var_1_35 )) < (( var_1_36 ))) ? (( var_1_35 )) : (( var_1_36 )))))))
  );
 } else {
                    var_1_33 = (
                     ((
    var_1_37
   ) - (
                      ((
     var_1_38
    ) - (
     var_1_39
    ))
   ))
  );
 }
                   if ( (( ((10.125) * (var_1_8))) < (var_1_8))) {
                    var_1_40 = (
                     ((
                      ((((( ((((var_1_43) < 0 ) ? -(var_1_43) : (var_1_43))) )) < (( ((((( var_1_44 )) < (( 31.7f ))) ? (( var_1_44 )) : (( 31.7f )))) ))) ? (( ((((var_1_43) < 0 ) ? -(var_1_43) : (var_1_43))) )) : (( ((((( var_1_44 )) < (( 31.7f ))) ? (( var_1_44 )) : (( 31.7f )))) ))))
   ) + (
                      ((((( ((((( var_1_45 )) < (( var_1_46 ))) ? (( var_1_45 )) : (( var_1_46 )))) )) < (( var_1_47 ))) ? (( ((((( var_1_45 )) < (( var_1_46 ))) ? (( var_1_45 )) : (( var_1_46 )))) )) : (( var_1_47 ))))
   ))
  );
 }
                   var_1_48 = (
  var_1_49
 );
                   var_1_50 = (
  1.4
 );
}
void updateVariables(void) {
 var_1_2 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_2 >= -2147483646);
 assume_abort_if_not(var_1_2 <= 2147483646);
 var_1_4 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_4 >= 0);
 assume_abort_if_not(var_1_4 <= 254);
 var_1_5 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_5 >= 0);
 assume_abort_if_not(var_1_5 <= 254);
 var_1_7 = __VERIFIER_nondet_ushort();
 assume_abort_if_not(var_1_7 >= 0);
 assume_abort_if_not(var_1_7 <= 32767);
 var_1_9 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_9 >= -2147483648);
 assume_abort_if_not(var_1_9 <= 2147483647);
 assume_abort_if_not(var_1_9 != 0);
 var_1_10 = __VERIFIER_nondet_double();
 assume_abort_if_not((var_1_10 >= 0.0F && var_1_10 <= -1.0e-20F) || (var_1_10 <= 4611686.018427383000e+12F && var_1_10 >= 1.0e-20F ));
 var_1_11 = __VERIFIER_nondet_double();
 assume_abort_if_not((var_1_11 >= 0.0F && var_1_11 <= -1.0e-20F) || (var_1_11 <= 4611686.018427383000e+12F && var_1_11 >= 1.0e-20F ));
 var_1_12 = __VERIFIER_nondet_double();
 assume_abort_if_not((var_1_12 >= 0.0F && var_1_12 <= -1.0e-20F) || (var_1_12 <= 4611686.018427383000e+12F && var_1_12 >= 1.0e-20F ));
 var_1_13 = __VERIFIER_nondet_double();
 assume_abort_if_not((var_1_13 >= 0.0F && var_1_13 <= -1.0e-20F) || (var_1_13 <= 4611686.018427383000e+12F && var_1_13 >= 1.0e-20F ));
 var_1_14 = __VERIFIER_nondet_double();
 assume_abort_if_not((var_1_14 >= 0.0F && var_1_14 <= -1.0e-20F) || (var_1_14 <= 4611686.018427383000e+12F && var_1_14 >= 1.0e-20F ));
 var_1_17 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_17 >= -63);
 assume_abort_if_not(var_1_17 <= 63);
 var_1_18 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_18 >= -31);
 assume_abort_if_not(var_1_18 <= 32);
 var_1_19 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_19 >= -31);
 assume_abort_if_not(var_1_19 <= 31);
 var_1_23 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_23 >= 0);
 assume_abort_if_not(var_1_23 <= 254);
 var_1_26 = __VERIFIER_nondet_ushort();
 assume_abort_if_not(var_1_26 >= 16383);
 assume_abort_if_not(var_1_26 <= 32767);
 var_1_27 = __VERIFIER_nondet_ushort();
 assume_abort_if_not(var_1_27 >= 16384);
 assume_abort_if_not(var_1_27 <= 32767);
 var_1_29 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_29 >= 0);
 assume_abort_if_not(var_1_29 <= 127);
 var_1_30 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_30 >= 0);
 assume_abort_if_not(var_1_30 <= 127);
 var_1_35 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_35 >= -126);
 assume_abort_if_not(var_1_35 <= 126);
 var_1_36 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_36 >= -126);
 assume_abort_if_not(var_1_36 <= 126);
 var_1_37 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_37 >= -1);
 assume_abort_if_not(var_1_37 <= 126);
 var_1_38 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_38 >= 63);
 assume_abort_if_not(var_1_38 <= 126);
 var_1_39 = __VERIFIER_nondet_char();
 assume_abort_if_not(var_1_39 >= 0);
 assume_abort_if_not(var_1_39 <= 63);
 var_1_43 = __VERIFIER_nondet_float();
 assume_abort_if_not((var_1_43 >= -461168.6018427383000e+13F && var_1_43 <= -1.0e-20F) || (var_1_43 <= 4611686.018427383000e+12F && var_1_43 >= 1.0e-20F ));
 var_1_44 = __VERIFIER_nondet_float();
 assume_abort_if_not((var_1_44 >= -461168.6018427383000e+13F && var_1_44 <= -1.0e-20F) || (var_1_44 <= 4611686.018427383000e+12F && var_1_44 >= 1.0e-20F ));
 var_1_45 = __VERIFIER_nondet_float();
 assume_abort_if_not((var_1_45 >= -461168.6018427383000e+13F && var_1_45 <= -1.0e-20F) || (var_1_45 <= 4611686.018427383000e+12F && var_1_45 >= 1.0e-20F ));
 var_1_46 = __VERIFIER_nondet_float();
 assume_abort_if_not((var_1_46 >= -461168.6018427383000e+13F && var_1_46 <= -1.0e-20F) || (var_1_46 <= 4611686.018427383000e+12F && var_1_46 >= 1.0e-20F ));
 var_1_47 = __VERIFIER_nondet_float();
 assume_abort_if_not((var_1_47 >= -461168.6018427383000e+13F && var_1_47 <= -1.0e-20F) || (var_1_47 <= 4611686.018427383000e+12F && var_1_47 >= 1.0e-20F ));
 var_1_49 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_49 >= 0);
 assume_abort_if_not(var_1_49 <= 0);
}
void updateLastVariables(void) {
 last_1_var_1_1 = var_1_1;
 last_1_var_1_6 = var_1_6;
 last_1_var_1_21 = var_1_21;
}
int property(void) {
 if ( ((var_1_1) < (var_1_2))) {
 }
 if ( (( ((var_1_2) ^ (var_1_1))) < (-256))) {
 } else {
  if ( ((var_1_5) <= (50))) {
  }
 }
 if ( ((var_1_1) < ( ((var_1_5) % ( (((((32)) > ((var_1_9))) ? ((32)) : ((var_1_9))))))))) {
 } else {
  if ( ((var_1_13) <= ( ((var_1_14) + (var_1_11))))) {
  }
 }
 if ( (( ((((var_1_4) < 0 ) ? -(var_1_4) : (var_1_4)))) > (last_1_var_1_1))) {
 }
 if ( ((var_1_15) == ( (( ((var_1_2) * (var_1_17))) & ( ((var_1_6) * (var_1_18))))))) {
 }
 return ((
             ((
              ((
               ((
                ((
                 ((
                  ((
                                         ((
        var_1_1
       ) == (
                                          ((signed long int) (
                                           ((((var_1_2) < 0 ) ? -(var_1_2) : (var_1_2)))
        ))
       ))
      ) && (
                                          ((
                                                ((
         var_1_1
        ) < (
         var_1_2
        ))
       ) ? (
                                           ((
         var_1_3
        ) == (
                                            ((unsigned char) (
                                             ((((( var_1_4 )) > (( var_1_5 ))) ? (( var_1_4 )) : (( var_1_5 ))))
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
         var_1_2
        ) ^ (
         var_1_1
        ))
       ) < (
        -256
       ))
      ) ? (
                                          ((
        var_1_6
       ) == (
                                           ((unsigned short int) (
                                            ((((((((( ((((( var_1_5 )) > (( var_1_4 ))) ? (( var_1_5 )) : (( var_1_4 )))) )) > (( (( last_1_var_1_6 ) + ( var_1_7 )) ))) ? (( ((((( var_1_5 )) > (( var_1_4 ))) ? (( var_1_5 )) : (( var_1_4 )))) )) : (( (( last_1_var_1_6 ) + ( var_1_7 )) ))))) < 0 ) ? -(((((( ((((( var_1_5 )) > (( var_1_4 ))) ? (( var_1_5 )) : (( var_1_4 )))) )) > (( (( last_1_var_1_6 ) + ( var_1_7 )) ))) ? (( ((((( var_1_5 )) > (( var_1_4 ))) ? (( var_1_5 )) : (( var_1_4 )))) )) : (( (( last_1_var_1_6 ) + ( var_1_7 )) ))))) : (((((( ((((( var_1_5 )) > (( var_1_4 ))) ? (( var_1_5 )) : (( var_1_4 )))) )) > (( (( last_1_var_1_6 ) + ( var_1_7 )) ))) ? (( ((((( var_1_5 )) > (( var_1_4 ))) ? (( var_1_5 )) : (( var_1_4 )))) )) : (( (( last_1_var_1_6 ) + ( var_1_7 )) )))))))
        ))
       ))
      ) : (
                                          ((
                                                ((
         var_1_5
        ) <= (
         50
        ))
       ) ? (
                                           ((
         var_1_6
        ) == (
                                            ((unsigned short int) (
          last_1_var_1_6
         ))
        ))
       ) : (
        1
       ))
      ))
     ))
    ) && (
                                         ((
                                              ((
       var_1_1
      ) < (
                                               ((
        var_1_5
       ) % (
                                                ((((( 32 )) > (( var_1_9 ))) ? (( 32 )) : (( var_1_9 ))))
       ))
      ))
     ) ? (
                                          ((
       var_1_8
      ) == (
                                           ((double) (
                                             ((
                                              ((
                                               ((((( var_1_10 )) > (( var_1_11 ))) ? (( var_1_10 )) : (( var_1_11 ))))
         ) - (
          var_1_12
         ))
        ) + (
                                              ((
          var_1_13
         ) - (
          var_1_14
         ))
        ))
       ))
      ))
     ) : (
                                           ((
                                                  ((
        var_1_13
       ) <= (
                                                   ((
         var_1_14
        ) + (
         var_1_11
        ))
       ))
      ) ? (
                                            ((
        var_1_8
       ) == (
                                             ((double) (
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
                                                           ((
                                                            ((((var_1_4) < 0 ) ? -(var_1_4) : (var_1_4)))
     ) > (
      last_1_var_1_1
     ))
    ) ? (
                                                     ((
      var_1_15
     ) == (
                                                      ((unsigned short int) (
                                                       ((((( last_1_var_1_21 )) > (( (( var_1_5 ) + ( var_1_4 )) ))) ? (( last_1_var_1_21 )) : (( (( var_1_5 ) + ( var_1_4 )) ))))
      ))
     ))
    ) : (
     1
    ))
   ))
  ) && (
                                        ((
    var_1_16
   ) == (
                                         ((signed char) (
                                          ((
      var_1_17
     ) + (
                                           ((
       var_1_18
      ) + (
                                            ((((var_1_19) < 0 ) ? -(var_1_19) : (var_1_19)))
      ))
     ))
    ))
   ))
  ))
 ) && (
                                       ((
   var_1_20
  ) == (
                                        ((unsigned short int) (
                                         ((((( (( var_1_5 ) + ( var_1_21 )) )) > (( var_1_4 ))) ? (( (( var_1_5 ) + ( var_1_21 )) )) : (( var_1_4 ))))
   ))
  ))
 ))
) && (
                                      ((
                                             ((
   var_1_15
  ) == (
                                              ((
                                               ((
     var_1_2
    ) * (
     var_1_17
    ))
   ) & (
                                               ((
     var_1_6
    ) * (
     var_1_18
    ))
   ))
  ))
 ) ? (
                                       ((
   var_1_21
  ) == (
                                        ((unsigned short int) (
                                         ((
     var_1_4
    ) + (
     128
    ))
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
