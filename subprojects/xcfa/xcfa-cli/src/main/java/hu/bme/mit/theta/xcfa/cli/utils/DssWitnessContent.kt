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
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.anytype.IteExpr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.AndExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.FalseExpr
import hu.bme.mit.theta.core.type.booltype.ImplyExpr
import hu.bme.mit.theta.core.type.booltype.NotExpr
import hu.bme.mit.theta.core.type.booltype.OrExpr
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs
import hu.bme.mit.theta.core.type.booltype.TrueExpr
import hu.bme.mit.theta.core.type.inttype.IntAddExpr
import hu.bme.mit.theta.core.type.inttype.IntEqExpr
import hu.bme.mit.theta.core.type.inttype.IntGeqExpr
import hu.bme.mit.theta.core.type.inttype.IntGtExpr
import hu.bme.mit.theta.core.type.inttype.IntLeqExpr
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.type.inttype.IntLtExpr
import hu.bme.mit.theta.core.type.inttype.IntMulExpr
import hu.bme.mit.theta.core.type.inttype.IntNegExpr
import hu.bme.mit.theta.core.type.inttype.IntNeqExpr
import hu.bme.mit.theta.core.type.inttype.IntSubExpr
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.analysis.dss.actor.DssInvariants
import hu.bme.mit.theta.xcfa.model.XcfaLocation
import hu.bme.mit.theta.xcfa.toC
import hu.bme.mit.theta.xcfa.utils.collectVars
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import hu.bme.mit.theta.xcfa.witnesses.*
import java.io.File
import java.math.BigInteger

/**
 * DSS's invariants at C statements that start an edge, where the program point is its source;
 * positions also used inside an edge, or with unknown states, are skipped.
 *
 * Each state keeps only the conjuncts that validators read as Theta does (see [isExactInC]), over
 * variables in scope at the position: dropping a conjunct weakens the state, so it stays valid.
 */
internal fun DssInvariants.toContent(
  inputFile: File,
  parseContext: ParseContext,
): List<ContentItem> {
  fun cNameOf(decl: VarDecl<*>) =
    parseContext.metadata.getMetadataValue(decl.name, "cName").orElse(null) as? String
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
  val sources = LinkedHashMap<Position, MutableSet<XcfaLocation>>()
  // The functions whose statement-declared locals a position's labels use (see [isInScope])
  val users = HashMap<Position, MutableSet<String>>()
  val inside = HashSet<Position>()
  for (edge in edges) {
    edge.label.getFlatLabels().forEachIndexed { index, label ->
      val metadata = label.metadata as? CMetaData ?: return@forEachIndexed
      val functions =
        label.collectVars().mapNotNullTo(hashSetOf()) { declaringFunction(it, parseContext) }
      for (statement in metadata.astNodes) {
        if (statement.lineNumberStart < 0 || statement.colNumberStart < 0) continue
        val position = Position(statement.lineNumberStart, statement.colNumberStart + 1)
        users.getOrPut(position) { hashSetOf() } += functions
        if (index == 0) sources.getOrPut(position) { linkedSetOf() } += edge.source
        else inside += position
      }
    }
  }
  return sources.mapNotNull { (position, locations) ->
    if (position in inside) return@mapNotNull null
    val function = users[position]?.singleOrNull()
    fun isUsable(decl: VarDecl<*>) =
      isCVar(decl) && isInScope(decl, function, position, parseContext)
    val states =
      locations
        .flatMap { invariants[it] ?: return@mapNotNull null }
        .map { state ->
          SmartBoolExprs.And(
            ExprUtils.getConjuncts(state).filter {
              isExactInC(it) && ExprUtils.getVars(it).all(::isUsable)
            }
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
          location = Location(inputFile.name, position.line, position.column),
          value = inC.toC(parseContext),
          format = Format.C_EXPRESSION,
        )
    )
  }
}

/** A statement's start in the input file; the column is 1-based, as in witnesses. */
private data class Position(val line: Int, val column: Int)

/** Where the statement declaring a local starts: absent for globals and parameters. */
private fun declaration(decl: VarDecl<*>, parseContext: ParseContext): Position? {
  val line = parseContext.metadata.getMetadataValue(decl.name, "locationLine").orElse(null)
  val column = parseContext.metadata.getMetadataValue(decl.name, "locationColumn").orElse(null)
  // The recorded column is 0-based
  return if (line is Int && column is Int) Position(line, column + 1) else null
}

/**
 * The C function whose statement declares [decl] (locals are named `function::...::name`), or null.
 * Parameters do not count: inlining assigns a callee's parameters at its call site.
 */
private fun declaringFunction(decl: VarDecl<*>, parseContext: ParseContext): String? {
  val segments = decl.name.split("::")
  if (segments.size < 2 || declaration(decl, parseContext) == null) return null
  return segments[0]
}

/**
 * Whether [decl] may be named at [position], a statement of C function [function] (null: unknown):
 * globals always, function-level locals and parameters of [function] once declared. The frontend
 * leaves statements' function names empty, so [function] comes from the locals the statement uses.
 * Block-scoped locals are named `function::block::name`; their block's extent is unknown.
 */
private fun isInScope(
  decl: VarDecl<*>,
  function: String?,
  position: Position,
  parseContext: ParseContext,
): Boolean {
  val segments = decl.name.split("::")
  if (segments.size == 1) return true
  if (segments.size != 2 || segments[0] != function) return false
  val declared = declaration(decl, parseContext) ?: return true
  return declared.line < position.line ||
    declared.line == position.line && declared.column < position.column
}

private val LONG_MAX = BigInteger.valueOf(Long.MAX_VALUE)

/**
 * Whether `toC` prints [expr] as a C expression with the same meaning: integer and Boolean terms
 * only. Bit-vector, floating-point and memory terms print with other semantics or not as C, integer
 * division and modulo follow SMT-LIB, and a literal must be a valid `long long` constant.
 */
private fun isExactInC(expr: Expr<*>): Boolean {
  val operands =
    when (expr) {
      is RefExpr<*> -> return expr.type == IntType.getInstance() || expr.type is BoolType
      is IntLitExpr -> return expr.value.abs() <= LONG_MAX
      is TrueExpr,
      is FalseExpr -> return true
      is AndExpr,
      is OrExpr,
      is NotExpr,
      is ImplyExpr,
      is IteExpr<*>,
      is IntEqExpr,
      is IntNeqExpr,
      is IntLtExpr,
      is IntLeqExpr,
      is IntGtExpr,
      is IntGeqExpr,
      is IntAddExpr,
      is IntSubExpr,
      is IntMulExpr,
      is IntNegExpr -> expr.ops
      else -> return false
    }
  return operands.all(::isExactInC)
}
