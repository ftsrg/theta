/*
 *  Copyright 2025 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.frontend.stdlib

internal val stdlib_h =
  """
typedef long int ptrdiff_t;
typedef long unsigned int size_t;
typedef int wchar_t;
typedef struct {
  long long __max_align_ll __attribute__((__aligned__(__alignof__(long long))));
  long double __max_align_ld __attribute__((__aligned__(__alignof__(long double))));
} max_align_t;
  typedef __typeof__(nullptr) nullptr_t;
typedef struct { int quot, rem; } div_t;
typedef struct { long quot, rem; } ldiv_t;
typedef struct { long long quot, rem; } lldiv_t;
extern double atof(const char *nptr);
extern int atoi(const char *nptr);
extern long int atol(const char *nptr);
extern long long int atoll(const char *nptr);
extern double strtod(const char * nptr, char ** endptr);
extern float strtof(const char * nptr, char ** endptr);
extern long double strtold(const char * nptr, char ** endptr);
extern long int strtol(const char * nptr, char ** endptr, int base);
extern long long int strtoll(const char * nptr, char ** endptr, int base);
extern unsigned long int strtoul(const char * nptr, char ** endptr, int base);
extern unsigned long long int strtoull(const char * nptr, char ** endptr, int base);
extern int rand(void);
extern void srand(unsigned int seed);
extern void *calloc(size_t nmemb, size_t size);
extern void free(void *ptr);
extern void *malloc(size_t size);
extern void *realloc(void *ptr, size_t size);
extern void abort(void);
extern int atexit(void (*func)(void));
extern void exit(int status);
extern void _Exit(int status);
extern char *getenv(const char *name);
extern int system(const char *string);
extern void *bsearch(const void *key, const void *base, size_t nmemb, size_t size, int (*compar)(const void *, const void *));
extern void qsort(void *base, size_t nmemb, size_t size, int (*compar)(const void *, const void *));
extern int abs(int j);
extern long int labs(long int j);
extern long long int llabs(long long int j);
extern div_t div(int numer, int denom);
extern ldiv_t ldiv(long int numer, long int denom);
extern lldiv_t lldiv(long long int numer, long long int denom);
extern int mblen(const char *s, size_t n);
"""
    .trimIndent()
