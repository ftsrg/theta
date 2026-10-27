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

import hu.bme.mit.theta.c2xcfa.CMetaData
import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.BasicSubstitution
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Or
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.analysis.*
import hu.bme.mit.theta.xcfa.analysis.dss.actor.DssInvariants
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import hu.bme.mit.theta.xcfa.toC
import hu.bme.mit.theta.xcfa.utils.collectVars
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import hu.bme.mit.theta.xcfa.witnesses.*
import java.io.File
import java.util.*

/**
 * DSS's invariants at C statements that start an edge, where the program point is its source;
 * positions also used inside an edge, or with unknown states, are skipped.
 */
internal fun DssInvariants.toContent(
  inputFile: File,
  parseContext: ParseContext,
): List<ContentItem> {
  fun cNameOf(decl: VarDecl<*>) = parseContext.variableSources[decl.name]?.cName
  // A C name shared by several variables (shadowing, same-named locals) cannot be resolved
  val edges = invariants.keys.flatMap { it.outgoingEdges }
  val shared =
    (edges.flatMap { it.label.collectVars() } +
        invariants.values.filterNotNull().flatten().flatMap { ExprUtils.getVars(it) })
      .toSet()
      .groupBy(::cNameOf)
      .filter { (name, vars) -> name != null && vars.size > 1 }
      .keys
  fun isCVar(decl: VarDecl<*>) = cNameOf(decl)?.let { it !in shared } ?: false
  val sources = LinkedHashMap<Pair<Int, Int>, MutableSet<XcfaLocation>>()
  val inside = HashSet<Pair<Int, Int>>()
  for (edge in edges) {
    edge.label.getFlatLabels().forEachIndexed { index, label ->
      for (statement in (label.metadata as? CMetaData)?.sourceStatements.orEmpty()) {
        if (statement.lineNumberStart < 0 || statement.colNumberStart < 0) continue
        val position = statement.lineNumberStart to statement.colNumberStart + 1
        if (index == 0) sources.getOrPut(position) { linkedSetOf() } += edge.source
        else inside += position
      }
    }
  }
  return sources.mapNotNull { (position, locations) ->
    if (position in inside) return@mapNotNull null
    // Only conjuncts over C variables are kept: that weakens each state, so it stays valid
    val states =
      locations
        .flatMap { invariants[it] ?: return@mapNotNull null }
        .map { state ->
          SmartBoolExprs.And(
            ExprUtils.getConjuncts(state).filter { ExprUtils.getVars(it).all(::isCVar) }
          )
        }
    val value = ExprUtils.simplify(SmartBoolExprs.Or(states))
    if (value == True()) return@mapNotNull null
    val inC =
      BasicSubstitution.builder()
        .apply { ExprUtils.getVars(value).forEach { put(it, Var(cNameOf(it)!!, it.type).ref) } }
        .build()
        .apply(value)
    ContentItem(
      invariant =
        Invariant(
          type = InvariantType.LOCATION_INVARIANT,
          location = Location(inputFile.name, position.first, position.second),
          value = inC.toC(parseContext),
          format = Format.C_EXPRESSION,
        )
    )
  }
}
