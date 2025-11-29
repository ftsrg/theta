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
void reach_error(void) { __assert_fail("0", "Req1_Prop1_Batch103Filler_PE_CI.c", 13, "reach_error"); }
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } return; }
void assume_abort_if_not(int cond) { if(!cond) { abort(); } }
void initially(void);
void step(void);
void updateVariables(void);
void updateLastVariables(void);
int property(void);
int main(void);
unsigned char isInitial = 0;
signed short int var_1_1 = 100;
signed long int var_1_2 = -500;
signed long int var_1_3 = -25;
signed short int var_1_6 = -64;
signed short int var_1_7 = 16;
signed short int var_1_8 = 20472;
signed short int var_1_9 = 16;
double var_1_10 = 1000000.9;
double var_1_11 = 0.0;
double var_1_12 = 0.0;
double var_1_13 = 7.25;
double var_1_14 = 64.4;
double var_1_15 = 15.625;
signed long int var_1_16 = 1000000;
signed long int var_1_17 = 128;
unsigned char var_1_18 = 100;
unsigned char var_1_20 = 1;
unsigned char var_1_21 = 10;
signed short int var_1_22 = -1;
signed char var_1_24 = -1;
unsigned short int var_1_25 = 0;
unsigned short int var_1_27 = 55769;
unsigned short int var_1_28 = 18537;
unsigned short int var_1_29 = 2;
signed short int var_1_30 = 1;
double var_1_31 = 10.4;
signed long int var_1_35 = -16;
unsigned long int var_1_38 = 25;
double var_1_39 = 127.5;
signed long int var_1_40 = 1;
double last_1_var_1_10 = 1000000.9;
void initially(void) {
}
void step(void) {
 signed long int stepLocal_0 = var_1_3;
                                         if ( ((var_1_2) <= (stepLocal_0))) {
                                          if ( (( (- (last_1_var_1_10))) >= (last_1_var_1_10))) {
                                           var_1_1 = (
    var_1_6
   );
  }
 } else {
                                          var_1_1 = (
                                           ((
    var_1_7
   ) - (
                                            ((
     var_1_8
    ) - (
     var_1_9
    ))
   ))
  );
 }
 signed short int stepLocal_1 = var_1_7;
                              if ( ((stepLocal_1) > (var_1_1))) {
                               var_1_10 = (
                                ((
                                 ((
     var_1_11
    ) - (
                                  ((
      var_1_12
     ) - (
      var_1_13
     ))
    ))
   ) - (
    3.25
   ))
  );
 } else {
                               var_1_10 = (
   var_1_11
  );
 }
                               if ( ((var_1_10) > (9.99999999928E9f))) {
                               var_1_14 = (
                                ((
                                 ((((( ((((( var_1_13 )) < (( 63.75 ))) ? (( var_1_13 )) : (( 63.75 )))) )) > (( (( var_1_12 ) + ( var_1_15 )) ))) ? (( ((((( var_1_13 )) < (( 63.75 ))) ? (( var_1_13 )) : (( 63.75 )))) )) : (( (( var_1_12 ) + ( var_1_15 )) ))))
   ) - (
    var_1_11
   ))
  );
 } else {
                                if ( ((var_1_12) <= (var_1_10))) {
                                 var_1_14 = (
    var_1_13
   );
  } else {
                                 var_1_14 = (
    var_1_11
   );
  }
 }
                               var_1_16 = (
                                ((
                                 ((((( (( var_1_8 ) + ( var_1_9 )) )) < (( var_1_7 ))) ? (( (( var_1_8 ) + ( var_1_9 )) )) : (( var_1_7 ))))
  ) - (
   var_1_17
  ))
 );
 signed long int stepLocal_2 = (~ (var_1_16));
                                if ( ((var_1_10) != ( ((var_1_13) - (var_1_11))))) {
                                 if ( ((stepLocal_2) > (var_1_16))) {
                                  var_1_22 = (
                                   ((
                                    ((
      var_1_21
     ) - (
      var_1_9
     ))
    ) + (
     var_1_16
    ))
   );
  } else {
                                  var_1_22 = (
                                   ((((( ((((( var_1_9 )) > (( var_1_6 ))) ? (( var_1_9 )) : (( var_1_6 )))) )) < (( var_1_16 ))) ? (( ((((( var_1_9 )) > (( var_1_6 ))) ? (( var_1_9 )) : (( var_1_6 )))) )) : (( var_1_16 ))))
   );
  }
 }
                                var_1_24 = (
  2
 );
                               if ( ((var_1_8) <= ( ((((( ((var_1_22) / (-500)))) > ((var_1_7))) ? (( ((var_1_22) / (-500)))) : ((var_1_7))))))) {
                                if (var_1_20) {
                                 var_1_18 = (
    var_1_21
   );
  }
 }
                  if ( (( ((var_1_27) - ( ((var_1_28) - (var_1_29))))) < ( ((50) % (-10000))))) {
                   var_1_25 = (
   var_1_29
  );
 }
                  var_1_30 = (
  var_1_29
 );
                   if ( ((var_1_28) >= (var_1_1))) {
                    var_1_31 = (
                     ((
    var_1_13
   ) - (
    var_1_12
   ))
  );
 } else {
                    var_1_31 = (
                     ((
    var_1_13
   ) + (
    -0.8
   ))
  );
 }
                   if ( (( ((16) << (10))) >= ( ((var_1_17) | (var_1_29))))) {
                    if (var_1_20) {
                     if ( (( ((2) << (var_1_16))) != ( ((var_1_3) | (var_1_8))))) {
                      var_1_35 = (
     var_1_16
    );
   }
  } else {
                     var_1_35 = (
    var_1_16
   );
  }
 }
                   if (var_1_20) {
                    if ( ((var_1_2) == ( (((((var_1_17)) > ((var_1_16))) ? ((var_1_17)) : ((var_1_16))))))) {
                     var_1_38 = (
                      ((((var_1_16) < 0 ) ? -(var_1_16) : (var_1_16)))
   );
  }
 }
                   if ( ((var_1_17) <= ( ((var_1_28) * ( (((((var_1_6)) > ((var_1_17))) ? ((var_1_6)) : ((var_1_17))))))))) {
                    var_1_39 = (
                     ((((9.5) < 0 ) ? -(9.5) : (9.5)))
  );
 }
                   if ( ((var_1_11) > ( ((((var_1_13) < 0 ) ? -(var_1_13) : (var_1_13)))))) {
                    if ( (( (((((var_1_13)) < (( ((var_1_13) / (var_1_11))))) ? ((var_1_13)) : (( ((var_1_13) / (var_1_11))))))) < (2.75))) {
                     var_1_40 = (
                      ((
     var_1_17
    ) + (
                       ((((( ((((( var_1_27 )) > (( var_1_29 ))) ? (( var_1_27 )) : (( var_1_29 )))) )) < (( var_1_7 ))) ? (( ((((( var_1_27 )) > (( var_1_29 ))) ? (( var_1_27 )) : (( var_1_29 )))) )) : (( var_1_7 ))))
    ))
   );
  }
 } else {
                    if ( ((var_1_16) <= (-2))) {
                     var_1_40 = (
    var_1_7
   );
  }
 }
}
void updateVariables(void) {
 var_1_2 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_2 >= -2147483648);
 assume_abort_if_not(var_1_2 <= 2147483647);
 var_1_3 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_3 >= -2147483648);
 assume_abort_if_not(var_1_3 <= 2147483647);
 var_1_6 = __VERIFIER_nondet_short();
 assume_abort_if_not(var_1_6 >= -32767);
 assume_abort_if_not(var_1_6 <= 32766);
 var_1_7 = __VERIFIER_nondet_short();
 assume_abort_if_not(var_1_7 >= -1);
 assume_abort_if_not(var_1_7 <= 32766);
 var_1_8 = __VERIFIER_nondet_short();
 assume_abort_if_not(var_1_8 >= 16383);
 assume_abort_if_not(var_1_8 <= 32766);
 var_1_9 = __VERIFIER_nondet_short();
 assume_abort_if_not(var_1_9 >= 0);
 assume_abort_if_not(var_1_9 <= 16383);
 var_1_11 = __VERIFIER_nondet_double();
 assume_abort_if_not((var_1_11 >= 4611686.018427383000e+12F && var_1_11 <= -1.0e-20F) || (var_1_11 <= 9223372.036854766000e+12F && var_1_11 >= 1.0e-20F ));
 var_1_12 = __VERIFIER_nondet_double();
 assume_abort_if_not((var_1_12 >= 2305843.009213691400e+12F && var_1_12 <= -1.0e-20F) || (var_1_12 <= 4611686.018427383000e+12F && var_1_12 >= 1.0e-20F ));
 var_1_13 = __VERIFIER_nondet_double();
 assume_abort_if_not((var_1_13 >= 0.0F && var_1_13 <= -1.0e-20F) || (var_1_13 <= 2305843.009213691400e+12F && var_1_13 >= 1.0e-20F ));
 var_1_15 = __VERIFIER_nondet_double();
 assume_abort_if_not((var_1_15 >= 0.0F && var_1_15 <= -1.0e-20F) || (var_1_15 <= 4611686.018427383000e+12F && var_1_15 >= 1.0e-20F ));
 var_1_17 = __VERIFIER_nondet_long();
 assume_abort_if_not(var_1_17 >= 0);
 assume_abort_if_not(var_1_17 <= 2147483646);
 var_1_20 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_20 >= 0);
 assume_abort_if_not(var_1_20 <= 1);
 var_1_21 = __VERIFIER_nondet_uchar();
 assume_abort_if_not(var_1_21 >= 0);
 assume_abort_if_not(var_1_21 <= 254);
 var_1_27 = __VERIFIER_nondet_ushort();
 assume_abort_if_not(var_1_27 >= 32767);
 assume_abort_if_not(var_1_27 <= 65535);
 var_1_28 = __VERIFIER_nondet_ushort();
 assume_abort_if_not(var_1_28 >= 16383);
 assume_abort_if_not(var_1_28 <= 32767);
 var_1_29 = __VERIFIER_nondet_ushort();
 assume_abort_if_not(var_1_29 >= 0);
 assume_abort_if_not(var_1_29 <= 16383);
}
void updateLastVariables(void) {
 last_1_var_1_10 = var_1_10;
}
int property(void) {
 if ( ((var_1_2) <= (var_1_3))) {
  if ( (( (- (last_1_var_1_10))) >= (last_1_var_1_10))) {
  }
 } else {
 }
 if ( ((var_1_7) > (var_1_1))) {
 } else {
 }
 if ( ((var_1_10) > (9.99999999928E9f))) {
 } else {
  if ( ((var_1_12) <= (var_1_10))) {
  } else {
  }
 }
 if ( ((var_1_8) <= ( ((((( ((var_1_22) / (-500)))) > ((var_1_7))) ? (( ((var_1_22) / (-500)))) : ((var_1_7))))))) {
  if (var_1_20) {
  }
 }
 if ( ((var_1_10) != ( ((var_1_13) - (var_1_11))))) {
  if ( (( (~ (var_1_16))) > (var_1_16))) {
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
        var_1_2
       ) <= (
        var_1_3
       ))
      ) ? (
                                                      ((
                                                            ((
                                                             (- (
          last_1_var_1_10
         ))
        ) >= (
         last_1_var_1_10
        ))
       ) ? (
                                                       ((
         var_1_1
        ) == (
                                                        ((signed short int) (
          var_1_6
         ))
        ))
       ) : (
        1
       ))
      ) : (
                                                      ((
        var_1_1
       ) == (
                                                       ((signed short int) (
                                                        ((
          var_1_7
         ) - (
                                                         ((
           var_1_8
          ) - (
           var_1_9
          ))
         ))
        ))
       ))
      ))
     ) && (
                                          ((
                                                ((
        var_1_7
       ) > (
        var_1_1
       ))
      ) ? (
                                           ((
        var_1_10
       ) == (
                                            ((double) (
                                             ((
                                              ((
           var_1_11
          ) - (
                                               ((
            var_1_12
           ) - (
            var_1_13
           ))
          ))
         ) - (
          3.25
         ))
        ))
       ))
      ) : (
                                           ((
        var_1_10
       ) == (
                                            ((double) (
         var_1_11
        ))
       ))
      ))
     ))
    ) && (
                                          ((
                                               ((
       var_1_10
      ) > (
       9.99999999928E9f
      ))
     ) ? (
                                          ((
       var_1_14
      ) == (
                                           ((double) (
                                            ((
                                             ((((( ((((( var_1_13 )) < (( 63.75 ))) ? (( var_1_13 )) : (( 63.75 )))) )) > (( (( var_1_12 ) + ( var_1_15 )) ))) ? (( ((((( var_1_13 )) < (( 63.75 ))) ? (( var_1_13 )) : (( 63.75 )))) )) : (( (( var_1_12 ) + ( var_1_15 )) ))))
        ) - (
         var_1_11
        ))
       ))
      ))
     ) : (
                                           ((
                                                ((
        var_1_12
       ) <= (
        var_1_10
       ))
      ) ? (
                                            ((
        var_1_14
       ) == (
                                             ((double) (
         var_1_13
        ))
       ))
      ) : (
                                            ((
        var_1_14
       ) == (
                                             ((double) (
         var_1_11
        ))
       ))
      ))
     ))
    ))
   ) && (
                                         ((
     var_1_16
    ) == (
                                          ((signed long int) (
                                           ((
                                            ((((( (( var_1_8 ) + ( var_1_9 )) )) < (( var_1_7 ))) ? (( (( var_1_8 ) + ( var_1_9 )) )) : (( var_1_7 ))))
      ) - (
       var_1_17
      ))
     ))
    ))
   ))
  ) && (
                                        ((
                                               ((
     var_1_8
    ) <= (
                                                ((((( (( var_1_22 ) / ( -500 )) )) > (( var_1_7 ))) ? (( (( var_1_22 ) / ( -500 )) )) : (( var_1_7 ))))
    ))
   ) ? (
                                         ((
     var_1_20
    ) ? (
                                          ((
      var_1_18
     ) == (
                                           ((unsigned char) (
       var_1_21
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
    var_1_10
   ) != (
                                               ((
     var_1_13
    ) - (
     var_1_11
    ))
   ))
  ) ? (
                                        ((
                                               ((
                                                (~ (
      var_1_16
     ))
    ) > (
     var_1_16
    ))
   ) ? (
                                         ((
     var_1_22
    ) == (
                                          ((signed short int) (
                                           ((
                                            ((
        var_1_21
       ) - (
        var_1_9
       ))
      ) + (
       var_1_16
      ))
     ))
    ))
   ) : (
                                         ((
     var_1_22
    ) == (
                                          ((signed short int) (
                                           ((((( ((((( var_1_9 )) > (( var_1_6 ))) ? (( var_1_9 )) : (( var_1_6 )))) )) < (( var_1_16 ))) ? (( ((((( var_1_9 )) > (( var_1_6 ))) ? (( var_1_9 )) : (( var_1_6 )))) )) : (( var_1_16 ))))
     ))
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
   2
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
