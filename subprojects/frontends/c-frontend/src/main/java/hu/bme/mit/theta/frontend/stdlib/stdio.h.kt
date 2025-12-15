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

internal val stdio_h =
  """
typedef long int ptrdiff_t;
typedef long unsigned int size_t;
typedef int wchar_t;
typedef struct {
  long long __max_align_ll __attribute__((__aligned__(__alignof__(long long))));
  long double __max_align_ld __attribute__((__aligned__(__alignof__(long double))));
} max_align_t;
  typedef __typeof__(nullptr) nullptr_t;
typedef __builtin_va_list __gnuc_va_list;
typedef __gnuc_va_list va_list;
typedef void FILE;
extern FILE *stdin, *stdout, *stderr;
typedef long fpos_t;
extern int remove(const char *filename);
extern int rename(const char *old, const char *new_);
extern FILE *tmpfile(void);
extern char *tmpnam(char *s);
extern int fclose(FILE *stream);
extern int fflush(FILE *stream);
extern FILE *fopen(const char * filename, const char * mode);
extern FILE *freopen(const char * filename, const char * mode, FILE * stream);
extern void setbuf(FILE * stream, char * buf);
extern int setvbuf(FILE * stream, char * buf, int mode, size_t size);
extern int fprintf(FILE * stream, const char * format, ...);
extern int fscanf(FILE * stream, const char * format, ...);
extern int printf(const char * format, ...);
extern int scanf(const char * format, ...);
extern int snprintf(char * s, size_t n, const char * format, ...);
extern int sprintf(char * s, const char * format, ...);
extern int sscanf(const char * s, const char * format, ...);
extern int vfprintf(FILE * stream, const char * format, va_list arg);
extern int vfscanf(FILE * stream, const char * format, va_list arg);
extern int vprintf(const char * format, va_list arg);
extern int vscanf(const char * format, va_list arg);
extern int vsnprintf(char * s, size_t n, const char * format, va_list arg);
extern int vsprintf(char * s, const char * format, va_list arg);
extern int vsscanf(const char * s, const char * format, va_list arg);
extern int fgetc(FILE *stream);
extern char *fgets(char * s, int n, FILE * stream);
extern int fputc(int c, FILE *stream);
extern int fputs(const char * s, FILE * stream);
extern int getc(FILE *stream);
extern int getchar(void);
extern char *gets(char *s);
extern int putc(int c, FILE *stream);
extern int putchar(int c);
extern int puts(const char *s);
extern int ungetc(int c, FILE *stream);
extern size_t fread(void * ptr, size_t size, size_t nmemb, FILE * stream);
extern size_t fwrite(const void * ptr, size_t size, size_t nmemb, FILE * stream);
extern int fgetpos(FILE * stream, fpos_t * pos);
extern int fseek(FILE *stream, long int offset, int whence);
extern int fsetpos(FILE *stream, const fpos_t *pos);
extern long int ftell(FILE *stream);
extern void rewind(FILE *stream);
extern void clearerr(FILE *stream);
extern int feof(FILE *stream);
extern int ferror(FILE *stream);
extern void perror(const char *s);
"""
    .trimIndent()
