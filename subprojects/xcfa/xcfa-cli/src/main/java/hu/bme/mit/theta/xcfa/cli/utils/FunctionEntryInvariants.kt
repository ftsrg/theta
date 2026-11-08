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
package hu.bme.mit.theta.xcfa.cli.utils

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.AndExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolExprs.False
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Or
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.analysis.proof.LocationInvariants
import hu.bme.mit.theta.xcfa.model.ParamDirection
import hu.bme.mit.theta.xcfa.model.XCFA

/** The invariant of one procedure's entry location, see [functionEntryInvariants]. */
internal data class FunctionEntryInvariant(
  val function: String,
  val parameters: List<String>,
  val states: Int,
  val invariant: Expr<BoolType>,
  val cExpression: String?,
)

/**
 * The proof states at the entry location of each procedure, projected to its input parameters and
 * the C globals, and joined. A conjunct over any other variable is dropped, which only weakens a
 * state, so the join stays an invariant of the entry. Theta's ghost globals (the memory arrays, the
 * pointer sizes) are not C globals and are dropped too. [FunctionEntryInvariant.cExpression] is set
 * when [CInvariantPrinter] can print the whole invariant exactly over the C names.
 */
internal fun LocationInvariants.functionEntryInvariants(
  xcfa: XCFA,
  parseContext: ParseContext,
): List<FunctionEntryInvariant> {
  fun cNameOf(decl: VarDecl<*>) =
    parseContext.metadata.getMetadataValue(decl.name, "cName").orElse(null) as? String
  val globals = xcfa.globalVars.map { it.wrappedVar }.filter { cNameOf(it) != null }
  return xcfa.procedures
    .sortedBy { it.name }
    .mapNotNull { procedure ->
      val states = partitions[procedure.initLoc] ?: return@mapNotNull null
      val params = procedure.params.filter { it.second != ParamDirection.OUT }.map { it.first }
      val kept = (params + globals).toSet()
      val disjuncts =
        states
          .filterNot { it.isBottom }
          .map { state ->
            And(conjuncts(state.toExpr()).filter { ExprUtils.getVars(it).all(kept::contains) })
          }
      val invariant =
        if (disjuncts.isEmpty()) False() else ExprUtils.simplify(Or(disjuncts.distinct()))
      val names = kept.mapNotNull { decl -> cNameOf(decl)?.let { decl to it } }.toMap()
      FunctionEntryInvariant(
        procedure.name,
        params.map { cNameOf(it) ?: it.name },
        disjuncts.size,
        invariant,
        CInvariantPrinter(names, parseContext).print(invariant),
      )
    }
}

private fun conjuncts(expr: Expr<BoolType>): List<Expr<BoolType>> =
  if (expr is AndExpr) expr.ops.flatMap(::conjuncts) else listOf(expr)

/** [invariants] as YAML, one entry per function. */
internal fun functionEntryInvariantsYaml(invariants: List<FunctionEntryInvariant>): String {
  fun quote(s: String) = "'" + s.replace("'", "''").replace(Regex("\\s+"), " ") + "'"
  return buildString {
    for (inv in invariants) {
      append("- function: ${quote(inv.function)}\n")
      append("  parameters: [${inv.parameters.joinToString(", ", transform = ::quote)}]\n")
      append("  states: ${inv.states}\n")
      append("  invariant: ${quote(inv.invariant.toString())}\n")
      inv.cExpression?.let { append("  c_expression: ${quote(it)}\n") }
    }
  }
}
