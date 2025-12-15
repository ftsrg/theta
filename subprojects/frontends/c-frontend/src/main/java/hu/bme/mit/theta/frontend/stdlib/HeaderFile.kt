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

import hu.bme.mit.theta.c.frontend.dsl.gen.CBaseVisitor
import hu.bme.mit.theta.c.frontend.dsl.gen.CLexer
import hu.bme.mit.theta.c.frontend.dsl.gen.CParser
import org.antlr.v4.runtime.BailErrorStrategy
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream

enum class HeaderFile(val filename: String, val content: String) {
  ASSERT_H("assert.h", assert_h),
  CTYPE_H("ctype.h", ctype_h),
  ERRNO_H("errno.h", errno_h),
  FLOAT_H("float.h", float_h),
  INTTYPES_H("inttypes.h", inttypes_h),
  LIMITS_H("limits.h", limits_h),
  MATH_H("math.h", math_h),
  PTHREAD_H("pthread.h", pthread_h),
  SETJMP_H("setjmp.h", setjmp_h),
  SIGNAL_H("signal.h", signal_h),
  STDARG_H("stdarg.h", stdarg_h),
  STDDEF_H("stddef.h", stddef_h),
  STDINT_H("stdint.h", stdint_h),
  STDIO_H("stdio.h", stdio_h),
  STDLIB_H("stdlib.h", stdlib_h),
  STRING_H("string.h", string_h),
  TIME_H("time.h", time_h),
}

private fun fromPath(s: String): String =
  HeaderFile.entries.firstOrNull() { it.filename == s }?.content ?: ""

private val includePattern = Regex("<(.*)>")

fun <T> parseHeaderFile(includeDirective: String, visitor: CBaseVisitor<T>): T? {
  val headerFile = includePattern.find(includeDirective)?.groupValues?.get(1) ?: return null
  val input = CharStreams.fromString(fromPath(headerFile))
  val lexer = CLexer(input)
  val tokens = CommonTokenStream(lexer)
  val parser = CParser(tokens)
  parser.setErrorHandler(BailErrorStrategy())
  val context = parser.translationUnit()
  return context.accept(visitor)
}
