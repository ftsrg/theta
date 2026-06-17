// This file is part of the SV-Benchmarks collection of verification tasks:
// https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks
//
// SPDX-FileCopyrightText: 2021 F. Schuessele <schuessf@informatik.uni-freiburg.de>
// SPDX-FileCopyrightText: 2021 D. Klumpp <klumpp@informatik.uni-freiburg.de>
//
// SPDX-License-Identifier: LicenseRef-BSD-3-Clause-Attribution-Vandikas

typedef unsigned long int pthread_t;

union pthread_attr_t
{
  char __size[36];
  long int __align;
};
typedef union pthread_attr_t pthread_attr_t;

extern void __assert_fail(const char *__assertion, const char *__file,
      unsigned int __line, const char *__function)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "chl-poker-hand-subst.wvr.c", 21, __extension__ __PRETTY_FUNCTION__); }
extern int pthread_create (pthread_t *__restrict __newthread,
      const pthread_attr_t *__restrict __attr,
      void *(*__start_routine) (void *),
      void *__restrict __arg) __attribute__ ((__nothrow__)) __attribute__ ((__nonnull__ (1, 3)));
extern int pthread_join (pthread_t __th, void **__thread_return);

typedef unsigned int size_t;
extern void *malloc (size_t __size) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;

extern int   __VERIFIER_nondet_int(void);
extern _Bool __VERIFIER_nondet_bool(void);
extern void  __VERIFIER_atomic_begin();
extern void  __VERIFIER_atomic_end();

extern void abort(void);
void assume_abort_if_not(int cond) {
  if(!cond) {abort();}
}

int *index_of_0, *char_at_1, *count_occurrences_of_2, *last_index_of_3, *index_of_4, *char_at_5, *count_occurrences_of_6, *last_index_of_7, *index_of_8, *char_at_9, *count_occurrences_of_10, *last_index_of_11;
int result_12, i1_13, i2_15, result_17, i1_18, i2_20, result_22, i1_23, i2_25;
_Bool break_14, break_16, break_19, break_21, break_24, break_26;

int *create_fresh_int_array(int size);

int minus(int a, int b);

void* thread1(void* _argptr) {
  if ( __VERIFIER_nondet_bool() ) {
    __VERIFIER_atomic_begin();
    assume_abort_if_not( ( ( index_of_0[4] != ( 0 - 1 ) ) || ( index_of_4[4] != ( 0 - 1 ) ) ) && ( index_of_0[4] == index_of_4[4] ) );
    i1_13 = 0;
    break_14 = 0;
    __VERIFIER_atomic_end();

    while ( __VERIFIER_nondet_bool() ) {
      __VERIFIER_atomic_begin();
      assume_abort_if_not( !break_14 && ( i1_13 <= 12 ) );
      result_12 = ( ( ( char_at_1[i1_13] != 0 ) && ( ( char_at_1[i1_13] != 4 ) && ( ( char_at_5[i1_13] != 0 ) && ( char_at_5[i1_13] != 4 ) ) ) ) ? 0 : ( ( ( char_at_1[i1_13] != 0 ) && ( char_at_1[i1_13] != 4 ) ) ? ( 0 - 1 ) : ( ( ( char_at_5[i1_13] != 0 ) && ( char_at_5[i1_13] != 4 ) ) ? 1 : result_12 ) ) );
      break_14 = ( ( ( ( char_at_1[i1_13] != 0 ) && ( char_at_1[i1_13] != 4 ) ) || ( ( char_at_5[i1_13] != 0 ) && ( char_at_5[i1_13] != 4 ) ) ) ? 1 : break_14 );
      i1_13 = ( i1_13 + 1 );
      __VERIFIER_atomic_end();
    }

    __VERIFIER_atomic_begin();
      assume_abort_if_not( !( !break_14 && ( i1_13 <= 12 ) ) );
      result_12 = ( (!break_14) ? minus(index_of_0[4], index_of_4[4]) : result_12 );
    __VERIFIER_atomic_end();
  }
  else if ( __VERIFIER_nondet_bool() ) {
    __VERIFIER_atomic_begin();
      assume_abort_if_not( ( ( index_of_0[4] != ( 0 - 1 ) ) || ( index_of_4[4] != ( 0 - 1 ) ) ) && !( index_of_0[4] == index_of_4[4] ) );
      result_12 = minus(index_of_0[4], index_of_4[4]);
    __VERIFIER_atomic_end();
  }
  else if ( __VERIFIER_nondet_bool() ) {
    __VERIFIER_atomic_begin();
      assume_abort_if_not( !( ( index_of_0[4] != ( 0 - 1 ) ) || ( index_of_4[4] != ( 0 - 1 ) ) ) );
      assume_abort_if_not( ( count_occurrences_of_2[3] > 1 ) || ( ( count_occurrences_of_2[3] == 1 ) && ( index_of_0[2] != ( 0 - 1 ) ) ) );
      assume_abort_if_not( ( count_occurrences_of_6[3] > 1 ) || ( ( count_occurrences_of_6[3] == 1 ) && ( index_of_4[2] != ( 0 - 1 ) ) ) );
      assume_abort_if_not( last_index_of_3[3] == last_index_of_7[3] );
      i2_15 = 0;
      break_16 = 0;
    __VERIFIER_atomic_end();
    while ( __VERIFIER_nondet_bool() ) {
      __VERIFIER_atomic_begin();
        assume_abort_if_not( !break_16 && ( i2_15 <= 12 ) );
        result_12 = ( ( ( i2_15 != last_index_of_3[3] ) && ( ( ( char_at_1[i2_15] == 2 ) || ( char_at_1[i2_15] == 3 ) ) && ( ( char_at_5[i2_15] == 2 ) || ( char_at_5[i2_15] == 3 ) ) ) ) ? 0 : ( ( ( i2_15 != last_index_of_3[3] ) && ( ( char_at_1[i2_15] == 2 ) || ( char_at_1[i2_15] == 3 ) ) ) ? ( 0 - 1 ) : ( ( ( i2_15 != last_index_of_3[3] ) && ( ( char_at_5[i2_15] == 2 ) || ( char_at_5[i2_15] == 3 ) ) ) ? 1 : result_12 ) ) );
        break_16 = ( ( ( i2_15 != last_index_of_3[3] ) && ( ( char_at_1[i2_15] == 2 ) || ( ( char_at_1[i2_15] == 3 ) || ( ( char_at_5[i2_15] == 2 ) || ( char_at_5[i2_15] == 3 ) ) ) ) ) ? 1 : break_16 );
      __VERIFIER_atomic_end();
    }
    __VERIFIER_atomic_begin();
      assume_abort_if_not( !( !break_16 && ( i2_15 <= 12 ) ) );
      result_12 = ( (!break_16) ? minus(last_index_of_3[3], last_index_of_7[3]) : result_12 );
    __VERIFIER_atomic_end();
  }
  else if ( __VERIFIER_nondet_bool() ) {
    __VERIFIER_atomic_begin();
      assume_abort_if_not( !( ( index_of_0[4] != ( 0 - 1 ) ) || ( index_of_4[4] != ( 0 - 1 ) ) ) );
      assume_abort_if_not( ( count_occurrences_of_2[3] > 1 ) || ( ( count_occurrences_of_2[3] == 1 ) && ( index_of_0[2] != ( 0 - 1 ) ) ) );
      assume_abort_if_not( ( count_occurrences_of_6[3] > 1 ) || ( ( count_occurrences_of_6[3] == 1 ) && ( index_of_4[2] != ( 0 - 1 ) ) ) );
      assume_abort_if_not( !( last_index_of_3[3] == last_index_of_7[3] ) );
      result_12 = minus(last_index_of_3[3], last_index_of_7[3]);
    __VERIFIER_atomic_end();
  }
  else if ( __VERIFIER_nondet_bool() ) {
    __VERIFIER_atomic_begin();
      assume_abort_if_not( !( ( index_of_0[4] != ( 0 - 1 ) ) || ( index_of_4[4] != ( 0 - 1 ) ) ) );
      assume_abort_if_not( ( count_occurrences_of_2[3] > 1 ) || ( ( count_occurrences_of_2[3] == 1 ) && ( index_of_0[2] != ( 0 - 1 ) ) ) );
      assume_abort_if_not( !( ( count_occurrences_of_6[3] > 1 ) || ( ( count_occurrences_of_6[3] == 1 ) && ( index_of_4[2] != ( 0 - 1 ) ) ) ) );
      result_12 = 1;
    __VERIFIER_atomic_end();
  }
  else if ( __VERIFIER_nondet_bool() ) {
    __VERIFIER_atomic_begin();
      assume_abort_if_not( !( ( index_of_0[4] != ( 0 - 1 ) ) || ( index_of_4[4] != ( 0 - 1 ) ) ) );
      assume_abort_if_not( !( ( count_occurrences_of_2[3] > 1 ) || ( ( count_occurrences_of_2[3] == 1 ) && ( index_of_0[2] != ( 0 - 1 ) ) ) ) );
      assume_abort_if_not( ( count_occurrences_of_6[3] > 1 ) || ( ( count_occurrences_of_6[3] == 1 ) && ( index_of_4[2] != ( 0 - 1 ) ) ) );
      result_12 = ( 0 - 1 );
    __VERIFIER_atomic_end();
  }
  else {
    __VERIFIER_atomic_begin();
      assume_abort_if_not( !( ( index_of_0[4] != ( 0 - 1 ) ) || ( index_of_4[4] != ( 0 - 1 ) ) ) );
      assume_abort_if_not( !( ( count_occurrences_of_2[3] > 1 ) || ( ( count_occurrences_of_2[3] == 1 ) && ( index_of_0[2] != ( 0 - 1 ) ) ) ) );
      assume_abort_if_not( !( ( count_occurrences_of_6[3] > 1 ) || ( ( count_occurrences_of_6[3] == 1 ) && ( index_of_4[2] != ( 0 - 1 ) ) ) ) );
      result_12 = 0;
    __VERIFIER_atomic_end();
  }

  return 0;
}

void* thread2(void* _argptr) {
  if ( __VERIFIER_nondet_bool() ) {
    __VERIFIER_atomic_begin();
      assume_abort_if_not( ( ( index_of_0[4] != ( 0 - 1 ) ) || ( index_of_8[4] != ( 0 - 1 ) ) ) && ( index_of_0[4] == index_of_8[4] ) );
      i1_18 = 0;
      break_19 = 0;
    __VERIFIER_atomic_end();
    while ( __VERIFIER_nondet_bool() ) {
      __VERIFIER_atomic_begin();
        assume_abort_if_not( !break_19 && ( i1_18 <= 12 ) );
        result_17 = ( ( ( char_at_1[i1_18] != 0 ) && ( ( char_at_1[i1_18] != 4 ) && ( ( char_at_9[i1_18] != 0 ) && ( char_at_9[i1_18] != 4 ) ) ) ) ? 0 : ( ( ( char_at_1[i1_18] != 0 ) && ( char_at_1[i1_18] != 4 ) ) ? ( 0 - 1 ) : ( ( ( char_at_9[i1_18] != 0 ) && ( char_at_9[i1_18] != 4 ) ) ? 1 : result_17 ) ) );
        break_19 = ( ( ( ( char_at_1[i1_18] != 0 ) && ( char_at_1[i1_18] != 4 ) ) || ( ( char_at_9[i1_18] != 0 ) && ( char_at_9[i1_18] != 4 ) ) ) ? 1 : break_19 );
        i1_18 = ( i1_18 + 1 );
    __VERIFIER_atomic_end();
    }
    __VERIFIER_atomic_begin();
      assume_abort_if_not( !( !break_19 && ( i1_18 <= 12 ) ) );
      result_17 = ( (!break_19) ? minus(index_of_0[4], index_of_8[4]) : result_17 );
    __VERIFIER_atomic_end();
  }
  else if ( __VERIFIER_nondet_bool() ) {
    __VERIFIER_atomic_begin();
      assume_abort_if_not( ( ( index_of_0[4] != ( 0 - 1 ) ) || ( index_of_8[4] != ( 0 - 1 ) ) ) && !( index_of_0[4] == index_of_8[4] ) );
      result_17 = minus(index_of_0[4], index_of_8[4]);
    __VERIFIER_atomic_end();
  }
  else if ( __VERIFIER_nondet_bool() ) {
    __VERIFIER_atomic_begin();
      assume_abort_if_not( !( ( index_of_0[4] != ( 0 - 1 ) ) || ( index_of_8[4] != ( 0 - 1 ) ) ) );
      assume_abort_if_not( ( count_occurrences_of_2[3] > 1 ) || ( ( count_occurrences_of_2[3] == 1 ) && ( index_of_0[2] != ( 0 - 1 ) ) ) );
      assume_abort_if_not( ( count_occurrences_of_10[3] > 1 ) || ( ( count_occurrences_of_10[3] == 1 ) && ( index_of_8[2] != ( 0 - 1 ) ) ) );
      assume_abort_if_not( last_index_of_3[3] == last_index_of_11[3] );
      i2_20 = 0;
      break_21 = 0;
    __VERIFIER_atomic_end();
    while ( __VERIFIER_nondet_bool() ) {
      __VERIFIER_atomic_begin();
        assume_abort_if_not( !break_21 && ( i2_20 <= 12 ) );
        result_17 = ( ( ( i2_20 != last_index_of_3[3] ) && ( ( ( char_at_1[i2_20] == 2 ) || ( char_at_1[i2_20] == 3 ) ) && ( ( char_at_9[i2_20] == 2 ) || ( char_at_9[i2_20] == 3 ) ) ) ) ? 0 : ( ( ( i2_20 != last_index_of_3[3] ) && ( ( char_at_1[i2_20] == 2 ) || ( char_at_1[i2_20] == 3 ) ) ) ? ( 0 - 1 ) : ( ( ( i2_20 != last_index_of_3[3] ) && ( ( char_at_9[i2_20] == 2 ) || ( char_at_9[i2_20] == 3 ) ) ) ? 1 : result_17 ) ) );
        break_21 = ( ( ( i2_20 != last_index_of_3[3] ) && ( ( char_at_1[i2_20] == 2 ) || ( ( char_at_1[i2_20] == 3 ) || ( ( char_at_9[i2_20] == 2 ) || ( char_at_9[i2_20] == 3 ) ) ) ) ) ? 1 : break_21 );
    __VERIFIER_atomic_end();
    }
    __VERIFIER_atomic_begin();
      assume_abort_if_not( !( !break_21 && ( i2_20 <= 12 ) ) );
      result_17 = ( (!break_21) ? minus(last_index_of_3[3], last_index_of_11[3]) : result_17 );
    __VERIFIER_atomic_end();
  }
  else if ( __VERIFIER_nondet_bool() ) {
    __VERIFIER_atomic_begin();
      assume_abort_if_not( !( ( index_of_0[4] != ( 0 - 1 ) ) || ( index_of_8[4] != ( 0 - 1 ) ) ) );
      assume_abort_if_not( ( count_occurrences_of_2[3] > 1 ) || ( ( count_occurrences_of_2[3] == 1 ) && ( index_of_0[2] != ( 0 - 1 ) ) ) );
      assume_abort_if_not( ( count_occurrences_of_10[3] > 1 ) || ( ( count_occurrences_of_10[3] == 1 ) && ( index_of_8[2] != ( 0 - 1 ) ) ) );
      assume_abort_if_not( !( last_index_of_3[3] == last_index_of_11[3] ) );
      result_17 = minus(last_index_of_3[3], last_index_of_11[3]);
    __VERIFIER_atomic_end();
  }
  else if ( __VERIFIER_nondet_bool() ) {
    __VERIFIER_atomic_begin();
      assume_abort_if_not( !( ( index_of_0[4] != ( 0 - 1 ) ) || ( index_of_8[4] != ( 0 - 1 ) ) ) );
      assume_abort_if_not( ( count_occurrences_of_2[3] > 1 ) || ( ( count_occurrences_of_2[3] == 1 ) && ( index_of_0[2] != ( 0 - 1 ) ) ) );
      assume_abort_if_not( !( ( count_occurrences_of_10[3] > 1 ) || ( ( count_occurrences_of_10[3] == 1 ) && ( index_of_8[2] != ( 0 - 1 ) ) ) ) );
      result_17 = 1;
    __VERIFIER_atomic_end();
  }
  else if ( __VERIFIER_nondet_bool() ) {
    __VERIFIER_atomic_begin();
      assume_abort_if_not( !( ( index_of_0[4] != ( 0 - 1 ) ) || ( index_of_8[4] != ( 0 - 1 ) ) ) );
      assume_abort_if_not( !( ( count_occurrences_of_2[3] > 1 ) || ( ( count_occurrences_of_2[3] == 1 ) && ( index_of_0[2] != ( 0 - 1 ) ) ) ) );
      assume_abort_if_not( ( count_occurrences_of_10[3] > 1 ) || ( ( count_occurrences_of_10[3] == 1 ) && ( index_of_8[2] != ( 0 - 1 ) ) ) );
      result_17 = ( 0 - 1 );
    __VERIFIER_atomic_end();
  }
  else {
    __VERIFIER_atomic_begin();
      assume_abort_if_not( !( ( index_of_0[4] != ( 0 - 1 ) ) || ( index_of_8[4] != ( 0 - 1 ) ) ) );
      assume_abort_if_not( !( ( count_occurrences_of_2[3] > 1 ) || ( ( count_occurrences_of_2[3] == 1 ) && ( index_of_0[2] != ( 0 - 1 ) ) ) ) );
      assume_abort_if_not( !( ( count_occurrences_of_10[3] > 1 ) || ( ( count_occurrences_of_10[3] == 1 ) && ( index_of_8[2] != ( 0 - 1 ) ) ) ) );
      result_17 = 0;
    __VERIFIER_atomic_end();
  }

  return 0;
}

void *thread3() {
  if ( __VERIFIER_nondet_bool() ) {
    __VERIFIER_atomic_begin();
      assume_abort_if_not( ( ( index_of_4[4] != ( 0 - 1 ) ) || ( index_of_8[4] != ( 0 - 1 ) ) ) && ( index_of_4[4] == index_of_8[4] ) );
      i1_23 = 0;
      break_24 = 0;
    __VERIFIER_atomic_end();
    while ( __VERIFIER_nondet_bool() ) {
      __VERIFIER_atomic_begin();
        assume_abort_if_not( !break_24 && ( i1_23 <= 12 ) );
        result_22 = ( ( ( char_at_5[i1_23] != 0 ) && ( ( char_at_5[i1_23] != 4 ) && ( ( char_at_9[i1_23] != 0 ) && ( char_at_9[i1_23] != 4 ) ) ) ) ? 0 : ( ( ( char_at_5[i1_23] != 0 ) && ( char_at_5[i1_23] != 4 ) ) ? ( 0 - 1 ) : ( ( ( char_at_9[i1_23] != 0 ) && ( char_at_9[i1_23] != 4 ) ) ? 1 : result_22 ) ) );
        break_24 = ( ( ( ( char_at_5[i1_23] != 0 ) && ( char_at_5[i1_23] != 4 ) ) || ( ( char_at_9[i1_23] != 0 ) && ( char_at_9[i1_23] != 4 ) ) ) ? 1 : break_24 );
        i1_23 = ( i1_23 + 1 );
    __VERIFIER_atomic_end();
    }
    __VERIFIER_atomic_begin();
      assume_abort_if_not( !( !break_24 && ( i1_23 <= 12 ) ) );
      result_22 = ( (!break_24) ? minus(index_of_4[4], index_of_8[4]) : result_22 );
    __VERIFIER_atomic_end();
  }
  else if ( __VERIFIER_nondet_bool() ) {
    __VERIFIER_atomic_begin();
      assume_abort_if_not( ( ( index_of_4[4] != ( 0 - 1 ) ) || ( index_of_8[4] != ( 0 - 1 ) ) ) && !( index_of_4[4] == index_of_8[4] ) );
      result_22 = minus(index_of_4[4], index_of_8[4]);
    __VERIFIER_atomic_end();
  }
  else if ( __VERIFIER_nondet_bool() ) {
    __VERIFIER_atomic_begin();
      assume_abort_if_not( !( ( index_of_4[4] != ( 0 - 1 ) ) || ( index_of_8[4] != ( 0 - 1 ) ) ) );
      assume_abort_if_not( ( count_occurrences_of_6[3] > 1 ) || ( ( count_occurrences_of_6[3] == 1 ) && ( index_of_4[2] != ( 0 - 1 ) ) ) );
      assume_abort_if_not( ( count_occurrences_of_10[3] > 1 ) || ( ( count_occurrences_of_10[3] == 1 ) && ( index_of_8[2] != ( 0 - 1 ) ) ) );
      assume_abort_if_not( last_index_of_7[3] == last_index_of_11[3] );
      i2_25 = 0;
      break_26 = 0;
    __VERIFIER_atomic_end();
    while ( __VERIFIER_nondet_bool() ) {
      __VERIFIER_atomic_begin();
        assume_abort_if_not( !break_26 && ( i2_25 <= 12 ) );
        result_22 = ( ( ( i2_25 != last_index_of_7[3] ) && ( ( ( char_at_5[i2_25] == 2 ) || ( char_at_5[i2_25] == 3 ) ) && ( ( char_at_9[i2_25] == 2 ) || ( char_at_9[i2_25] == 3 ) ) ) ) ? 0 : ( ( ( i2_25 != last_index_of_7[3] ) && ( ( char_at_5[i2_25] == 2 ) || ( char_at_5[i2_25] == 3 ) ) ) ? ( 0 - 1 ) : ( ( ( i2_25 != last_index_of_7[3] ) && ( ( char_at_9[i2_25] == 2 ) || ( char_at_9[i2_25] == 3 ) ) ) ? 1 : result_22 ) ) );
        break_26 = ( ( ( i2_25 != last_index_of_7[3] ) && ( ( char_at_5[i2_25] == 2 ) || ( ( char_at_5[i2_25] == 3 ) || ( ( char_at_9[i2_25] == 2 ) || ( char_at_9[i2_25] == 3 ) ) ) ) ) ? 1 : break_26 );
    __VERIFIER_atomic_end();
    }
    __VERIFIER_atomic_begin();
      assume_abort_if_not( !( !break_26 && ( i2_25 <= 12 ) ) );
      result_22 = ( (!break_26) ? minus(last_index_of_7[3], last_index_of_11[3]) : result_22 );
    __VERIFIER_atomic_end();
  }
  else if ( __VERIFIER_nondet_bool() ) {
    __VERIFIER_atomic_begin();
      assume_abort_if_not( !( ( index_of_4[4] != ( 0 - 1 ) ) || ( index_of_8[4] != ( 0 - 1 ) ) ) );
      assume_abort_if_not( ( count_occurrences_of_6[3] > 1 ) || ( ( count_occurrences_of_6[3] == 1 ) && ( index_of_4[2] != ( 0 - 1 ) ) ) );
      assume_abort_if_not( ( count_occurrences_of_10[3] > 1 ) || ( ( count_occurrences_of_10[3] == 1 ) && ( index_of_8[2] != ( 0 - 1 ) ) ) );
      assume_abort_if_not( !( last_index_of_7[3] == last_index_of_11[3] ) );
      result_22 = minus(last_index_of_7[3], last_index_of_11[3]);
    __VERIFIER_atomic_end();
  }
  else if ( __VERIFIER_nondet_bool() ) {
    __VERIFIER_atomic_begin();
      assume_abort_if_not( !( ( index_of_4[4] != ( 0 - 1 ) ) || ( index_of_8[4] != ( 0 - 1 ) ) ) );
      assume_abort_if_not( ( count_occurrences_of_6[3] > 1 ) || ( ( count_occurrences_of_6[3] == 1 ) && ( index_of_4[2] != ( 0 - 1 ) ) ) );
      assume_abort_if_not( !( ( count_occurrences_of_10[3] > 1 ) || ( ( count_occurrences_of_10[3] == 1 ) && ( index_of_8[2] != ( 0 - 1 ) ) ) ) );
      result_22 = 1;
    __VERIFIER_atomic_end();
  }
  else if ( __VERIFIER_nondet_bool() ) {
    __VERIFIER_atomic_begin();
      assume_abort_if_not( !( ( index_of_4[4] != ( 0 - 1 ) ) || ( index_of_8[4] != ( 0 - 1 ) ) ) );
      assume_abort_if_not( !( ( count_occurrences_of_6[3] > 1 ) || ( ( count_occurrences_of_6[3] == 1 ) && ( index_of_4[2] != ( 0 - 1 ) ) ) ) );
      assume_abort_if_not( ( count_occurrences_of_10[3] > 1 ) || ( ( count_occurrences_of_10[3] == 1 ) && ( index_of_8[2] != ( 0 - 1 ) ) ) );
      result_22 = ( 0 - 1 );
    __VERIFIER_atomic_end();
  }
  else {
    __VERIFIER_atomic_begin();
      assume_abort_if_not( !( ( index_of_4[4] != ( 0 - 1 ) ) || ( index_of_8[4] != ( 0 - 1 ) ) ) );
      assume_abort_if_not( !( ( count_occurrences_of_6[3] > 1 ) || ( ( count_occurrences_of_6[3] == 1 ) && ( index_of_4[2] != ( 0 - 1 ) ) ) ) );
      assume_abort_if_not( !( ( count_occurrences_of_10[3] > 1 ) || ( ( count_occurrences_of_10[3] == 1 ) && ( index_of_8[2] != ( 0 - 1 ) ) ) ) );
      result_22 = 0;
    __VERIFIER_atomic_end();
  }

  return 0;
}

int main() {
  pthread_t t1, t2, t3;

  // initialize global variables
  index_of_0 = create_fresh_int_array(5);
  index_of_4 = create_fresh_int_array(5);
  index_of_8 = create_fresh_int_array(5);
  char_at_1 = create_fresh_int_array(13);
  char_at_5 = create_fresh_int_array(13);
  char_at_9 = create_fresh_int_array(13);
  count_occurrences_of_2 = create_fresh_int_array(4);
  count_occurrences_of_6 = create_fresh_int_array(4);
  count_occurrences_of_10 = create_fresh_int_array(4);
  last_index_of_3 = create_fresh_int_array(4);
  last_index_of_7 = create_fresh_int_array(4);
  last_index_of_11 = create_fresh_int_array(4);
  result_12 = __VERIFIER_nondet_int();
  i1_13 = __VERIFIER_nondet_int();
  i2_15 = __VERIFIER_nondet_int();
  result_17 = __VERIFIER_nondet_int();
  i1_18 = __VERIFIER_nondet_int();
  i2_20 = __VERIFIER_nondet_int();
  result_22 = __VERIFIER_nondet_int();
  i1_23 = __VERIFIER_nondet_int();
  i2_25 = __VERIFIER_nondet_int();
  break_14 = __VERIFIER_nondet_bool();
  break_16 = __VERIFIER_nondet_bool();
  break_19 = __VERIFIER_nondet_bool();
  break_21 = __VERIFIER_nondet_bool();
  break_24 = __VERIFIER_nondet_bool();
  break_26 = __VERIFIER_nondet_bool();

  // main method
  pthread_create(&t1, 0, thread1, 0);
  pthread_create(&t2, 0, thread2, 0);
  pthread_create(&t3, 0, thread3, 0);
  pthread_join(t1, 0);
  pthread_join(t2, 0);
  pthread_join(t3, 0);

  assume_abort_if_not( !( !( result_12 == 0 ) || ( ( ( result_17 > 0 ) == ( result_22 > 0 ) ) && ( ( result_17 < 0 ) == ( result_22 < 0 ) ) ) ) );
  reach_error();

  return 0;
}

int *create_fresh_int_array(int size) {
  assume_abort_if_not(size >= 0);
  assume_abort_if_not(size <= (((size_t) 4294967295) / sizeof(int)));

  int* arr = (int*)malloc(sizeof(int) * (size_t)size);
  for (int i = 0; i < size; i++) {
    arr[i] = __VERIFIER_nondet_int();
  }
  return arr;
}

int minus(int a, int b) {
  assume_abort_if_not(b <= 0 || a >= b - 2147483648);
  assume_abort_if_not(b >= 0 || a <= b + 2147483647);
  return a - b;
}