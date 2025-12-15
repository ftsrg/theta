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

internal val string_h =
  """
typedef long int ptrdiff_t;
typedef long unsigned int size_t;
typedef int wchar_t;
typedef struct {
  long long __max_align_ll __attribute__((__aligned__(__alignof__(long long))));
  long double __max_align_ld __attribute__((__aligned__(__alignof__(long double))));
} max_align_t;
  typedef __typeof__(nullptr) nullptr_t;
extern void *memcpy(void * s1, const void * s2, size_t n);
extern void *memmove(void *s1, const void *s2, size_t n);
extern char *strcpy(char * s1, const char * s2);
extern char *strncpy(char * s1, const char * s2, size_t n);
extern char *strcat(char * s1, const char * s2);
extern char *strncat(char * s1, const char * s2, size_t n);
extern int memcmp(const void *s1, const void *s2, size_t n);
extern int strcmp(const char *s1, const char *s2);
extern int strcoll(const char *s1, const char *s2);
extern int strncmp(const char *s1, const char *s2, size_t n);
extern size_t strxfrm(char * s1, const char * s2, size_t n);
extern void *memchr(const void *s, int c, size_t n);
extern char *strchr(const char *s, int c);
extern size_t strcspn(const char *s1, const char *s2);
extern char *strpbrk(const char *s1, const char *s2);
extern char *strrchr(const char *s, int c);
extern size_t strspn(const char *s1, const char *s2);
extern char *strstr(const char *s1, const char *s2);
extern char *strtok(char * s1, const char * s2);
extern void *memset(void *s, int c, size_t n);
extern char *strerror(int errnum);
extern size_t strlen(const char *s);
"""
    .trimIndent()
