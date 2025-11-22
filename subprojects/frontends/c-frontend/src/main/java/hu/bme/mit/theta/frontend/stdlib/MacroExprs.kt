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

import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.grammar.expression.UnsupportedInitializer
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType

enum class MacroExprs(val id: String, val value: (ParseContext) -> Expr<*>) {

  PTHREAD_MUTEX_INITIALIZER("PTHREAD_MUTEX_INITIALIZER", { UnsupportedInitializer() }),
  NULL("NULL", { CComplexType.getSignedInt(it).nullValue }),

  // Integer characteristics
  CHAR_BIT("CHAR_BIT", { CComplexType.getSignedInt(it).getValue("8") }),
  CHAR_MAX("CHAR_MAX", { CComplexType.getSignedInt(it).getValue("127") }),
  CHAR_MIN("CHAR_MIN", { CComplexType.getSignedInt(it).getValue("-127") }),

  // Floating-point — double
  DBL_DIG("DBL_DIG", { CComplexType.getSignedInt(it).getValue("15") }),
  DBL_EPSILON("DBL_EPSILON", { CComplexType.getDouble(it).getValue("1.1102230246251568e-16") }),
  DBL_MANT_DIG("DBL_MANT_DIG", { CComplexType.getSignedInt(it).getValue("53") }),
  DBL_MAX("DBL_MAX", { CComplexType.getDouble(it).getValue("1.7976931348623157e+308") }),
  DBL_MAX_10_EXP("DBL_MAX_10_EXP", { CComplexType.getSignedInt(it).getValue("308") }),
  DBL_MAX_EXP("DBL_MAX_EXP", { CComplexType.getSignedInt(it).getValue("1024") }),
  DBL_MIN("DBL_MIN", { CComplexType.getDouble(it).getValue("2.2250738585072014e-308") }),
  DBL_MIN_10_EXP("DBL_MIN_10_EXP", { CComplexType.getSignedInt(it).getValue("-307") }),
  DBL_MIN_EXP("DBL_MIN_EXP", { CComplexType.getSignedInt(it).getValue("-1021") }),

  // EOF
  EOF("EOF", { CComplexType.getSignedInt(it).getValue("-1") }),

  // Floating-point — float
  FLT_DIG("FLT_DIG", { CComplexType.getSignedInt(it).getValue("6") }),
  FLT_EPSILON("FLT_EPSILON", { CComplexType.getFloat(it).getValue("1.19209290e-07F") }),
  FLT_GUARD("FLT_GUARD", { CComplexType.getSignedInt(it).getValue("1") }),
  FLT_MANT_DIG("FLT_MANT_DIG", { CComplexType.getSignedInt(it).getValue("24") }),
  FLT_MAX("FLT_MAX", { CComplexType.getFloat(it).getValue("3.40282347e+38F") }),
  FLT_MAX_10_EXP("FLT_MAX_10_EXP", { CComplexType.getSignedInt(it).getValue("38") }),
  FLT_MAX_EXP("FLT_MAX_EXP", { CComplexType.getSignedInt(it).getValue("128") }),
  FLT_MIN("FLT_MIN", { CComplexType.getFloat(it).getValue("1.17549435e-38F") }),
  FLT_MIN_10_EXP("FLT_MIN_10_EXP", { CComplexType.getSignedInt(it).getValue("-37") }),
  FLT_MIN_EXP("FLT_MIN_EXP", { CComplexType.getSignedInt(it).getValue("-125") }),
  FLT_NORMALIZE("FLT_NORMALIZE", { CComplexType.getSignedInt(it).getValue("1") }),
  FLT_RADIX("FLT_RADIX", { CComplexType.getSignedInt(it).getValue("2") }),
  FLT_ROUNDS("FLT_ROUNDS", { CComplexType.getSignedInt(it).getValue("1") }),

  // int, long, long long limits
  INT_MAX("INT_MAX", { CComplexType.getSignedInt(it).getValue("32767") }),
  INT_MIN("INT_MIN", { CComplexType.getSignedInt(it).getValue("-32767") }),
  LONG_MAX("LONG_MAX", { CComplexType.getSignedLong(it).getValue("2147483647") }),
  LONG_MIN("LONG_MIN", { CComplexType.getSignedLong(it).getValue("-2147483647") }),
  LLONG_MAX("LLONG_MAX", { CComplexType.getSignedLongLong(it).getValue("9223372036854775807") }),
  LLONG_MIN("LLONG_MIN", { CComplexType.getSignedLongLong(it).getValue("-9223372036854775807") }),

  // long double
  LDBL_DIG("LDBL_DIG", { CComplexType.getSignedInt(it).getValue("15") }),
  LDBL_EPSILON(
    "LDBL_EPSILON",
    { CComplexType.getLongDouble(it).getValue("1.1102230246251568e-16L") },
  ),
  LDBL_MANT_DIG("LDBL_MANT_DIG", { CComplexType.getSignedInt(it).getValue("53") }),
  LDBL_MAX("LDBL_MAX", { CComplexType.getLongDouble(it).getValue("1.7976931348623157e+308L") }),
  LDBL_MAX_10_EXP("LDBL_MAX_10_EXP", { CComplexType.getSignedInt(it).getValue("308") }),
  LDBL_MAX_EXP("LDBL_MAX_EXP", { CComplexType.getSignedInt(it).getValue("1024") }),
  LDBL_MIN("LDBL_MIN", { CComplexType.getLongDouble(it).getValue("2.2250738585072014e-308L") }),
  LDBL_MIN_10_EXP("LDBL_MIN_10_EXP", { CComplexType.getSignedInt(it).getValue("-307") }),
  LDBL_MIN_EXP("LDBL_MIN_EXP", { CComplexType.getSignedInt(it).getValue("-1021") }),
  MB_LEN_MAX("MB_LEN_MAX", { CComplexType.getSignedInt(it).getValue("1") }),

  // Printf macros — just strings
  PRId16("PRId16", { CComplexType.getSignedInt(it).getValue("\"d\"") }),
  PRId32("PRId32", { CComplexType.getSignedInt(it).getValue("\"d\"") }),
  PRId64("PRId64", { CComplexType.getSignedInt(it).getValue("\"I64d\"") }),
  PRId8("PRId8", { CComplexType.getSignedInt(it).getValue("\"d\"") }),
  PRIdMAX("PRIdMAX", { CComplexType.getSignedInt(it).getValue("\"I64d\"") }),
  PRIdPTR("PRIdPTR", { CComplexType.getSignedInt(it).getValue("\"d\"") }),
  PRIiMAX("PRIiMAX", { CComplexType.getSignedInt(it).getValue("\"I64i\"") }),
  PRIiPTR("PRIiPTR", { CComplexType.getSignedInt(it).getValue("\"i\"") }),
  PRIo16("PRIo16", { CComplexType.getSignedInt(it).getValue("\"o\"") }),
  PRIo32("PRIo32", { CComplexType.getSignedInt(it).getValue("\"o\"") }),
  PRIo64("PRIo64", { CComplexType.getSignedInt(it).getValue("\"I64o\"") }),
  PRIo8("PRIo8", { CComplexType.getSignedInt(it).getValue("\"o\"") }),
  PRIoPTR("PRIoPTR", { CComplexType.getSignedInt(it).getValue("\"o\"") }),
  PRIu16("PRIu16", { CComplexType.getSignedInt(it).getValue("\"u\"") }),
  PRIu32("PRIu32", { CComplexType.getSignedInt(it).getValue("\"u\"") }),
  PRIu64("PRIu64", { CComplexType.getSignedInt(it).getValue("\"I64u\"") }),
  PRIu8("PRIu8", { CComplexType.getSignedInt(it).getValue("\"u\"") }),
  PRIx16("PRIx16", { CComplexType.getSignedInt(it).getValue("\"x\"") }),
  PRIx32("PRIx32", { CComplexType.getSignedInt(it).getValue("\"x\"") }),
  PRIx64("PRIx64", { CComplexType.getSignedInt(it).getValue("\"I64x\"") }),
  PRIx8("PRIx8", { CComplexType.getSignedInt(it).getValue("\"x\"") }),
  PRIxPTR("PRIxPTR", { CComplexType.getSignedInt(it).getValue("\"x\"") }),

  // signed and unsigned char / short / int
  SCHAR_MAX("SCHAR_MAX", { CComplexType.getSignedInt(it).getValue("127") }),
  SCHAR_MIN("SCHAR_MIN", { CComplexType.getSignedInt(it).getValue("-127") }),
  SHRT_MAX("SHRT_MAX", { CComplexType.getSignedInt(it).getValue("32767") }),
  SHRT_MIN("SHRT_MIN", { CComplexType.getSignedInt(it).getValue("-32767") }),
  UCHAR_MAX("UCHAR_MAX", { CComplexType.getUnsignedInt(it).getValue("255") }),
  UINT_MAX("UINT_MAX", { CComplexType.getUnsignedInt(it).getValue("65535") }),
  ULLONG_MAX(
    "ULLONG_MAX",
    { CComplexType.getUnsignedLongLong(it).getValue("18446744073709551615") },
  ),
  ULONG_MAX("ULONG_MAX", { CComplexType.getUnsignedLong(it).getValue("4294967295") }),
  USHRT_MAX("USHRT_MAX", { CComplexType.getUnsignedInt(it).getValue("65535") }),
}

fun fromName(s: String, parseContext: ParseContext): Expr<*>? =
  MacroExprs.entries.firstOrNull() { it.id == s }?.value?.invoke(parseContext)
