/*
 *  Copyright 2026 Budapest University of Technology and Economics
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

import hu.bme.mit.theta.c.frontend.dsl.gen.CLexer
import hu.bme.mit.theta.c.frontend.dsl.gen.CParser
import org.antlr.v4.runtime.BailErrorStrategy
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream

/**
 * C definitions of library functions whose behaviour a verdict can depend on. The frontend adds the
 * one for a function the program declares but does not define, so it is analysed rather than
 * stubbed with an unconstrained return value -- which made `!strcmp(a, b)` true for different
 * strings and produced false alarms.
 *
 * Only plain types are used (`unsigned long` for `size_t`, the same width in ILP32 and LP64), so a
 * model parses without the program's typedefs. Adapted from the cir2c operational models.
 */
private val models: Map<String, String> =
  mapOf(
    "strlen" to
      """
      unsigned long strlen(const char *s) {
        unsigned long n = 0;
        while (s[n] != 0) n++;
        return n;
      }
      """,
    "strnlen" to
      """
      unsigned long strnlen(const char *s, unsigned long max) {
        unsigned long n = 0;
        while (n < max && s[n] != 0) n++;
        return n;
      }
      """,
    "strcmp" to
      """
      int strcmp(const char *a, const char *b) {
        unsigned long i = 0;
        while (a[i] != 0 && a[i] == b[i]) i++;
        return (int) (unsigned char) a[i] - (int) (unsigned char) b[i];
      }
      """,
    "strncmp" to
      """
      int strncmp(const char *a, const char *b, unsigned long n) {
        unsigned long i = 0;
        while (i < n && a[i] != 0 && a[i] == b[i]) i++;
        if (i == n) return 0;
        return (int) (unsigned char) a[i] - (int) (unsigned char) b[i];
      }
      """,
    "memcmp" to
      """
      int memcmp(const void *p, const void *q, unsigned long n) {
        const unsigned char *a = p;
        const unsigned char *b = q;
        for (unsigned long i = 0; i < n; i++) {
          if (a[i] != b[i]) return (int) a[i] - (int) b[i];
        }
        return 0;
      }
      """,
    "memchr" to
      """
      void *memchr(const void *s, int c, unsigned long n) {
        const unsigned char *p = s;
        for (unsigned long i = 0; i < n; i++) {
          if (p[i] == (unsigned char) c) return (void *) (p + i);
        }
        return 0;
      }
      """,
  )

/** The parsed definition of the model of [name], or null if there is none. */
fun libraryModel(name: String): CParser.ExternalDeclarationContext? {
  val source = models[name] ?: return null
  val parser = CParser(CommonTokenStream(CLexer(CharStreams.fromString(source.trimIndent()))))
  parser.setErrorHandler(BailErrorStrategy())
  return parser.translationUnit().externalDeclaration(0)
}
