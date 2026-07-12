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
package hu.bme.mit.theta.xcfa.passes

import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.TrueExpr
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.UnsupportedFrontendElementException
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig.getLimitVisitor
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.xcfa.model.MetaData
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.model.XcfaLabel

/**
 * States that a havoced value is one its C type can actually hold.
 *
 * A havoc on its own is unbounded, and under integer arithmetic that is *not* the same as a C
 * value: a `long long` becomes an arbitrary mathematical integer, with nothing saying it is at most
 * `LLONG_MAX`. Code that bounds such a value from one side only -- `if (a > -3037000500 && llabs(a)
 * <= 3037000499)` -- is then not bounded at all, and the analysis "finds" an overflow at a value no
 * C program could have produced. (Under bitvector arithmetic the width does this for us, so the
 * limit visitor yields `true` there and this costs nothing.)
 */
fun withinTypeRange(
  value: Expr<*>,
  parseContext: ParseContext,
  metadata: MetaData,
): List<XcfaLabel> {
  // Only when the C type is actually known. Without it, `getType` guesses from the SMT type, and a
  // guess is no basis for constraining a value.
  val cType =
    parseContext.metadata.getMetadataValue(value, "cType").orElse(null) as? CComplexType
      ?: return listOf()
  // Only integer types have a range to speak of. The integer limit visitor has no catch-all and
  // throws on anything else (a pointer, a struct), so a type it does not know simply goes
  // unconstrained -- as it did before.
  val assume =
    try {
      cType.accept(getLimitVisitor(parseContext), value)
    } catch (e: UnsupportedFrontendElementException) {
      return listOf()
    }
  if (assume.cond is TrueExpr) {
    return listOf()
  }
  return listOf(StmtLabel(assume, metadata = metadata))
}
