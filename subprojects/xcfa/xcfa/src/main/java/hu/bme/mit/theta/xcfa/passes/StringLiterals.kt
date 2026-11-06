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

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AddExpr
import hu.bme.mit.theta.core.type.abstracttype.PosExpr
import hu.bme.mit.theta.core.type.anytype.IteExpr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.bvtype.BvExtractExpr
import hu.bme.mit.theta.core.type.bvtype.BvPosExpr
import hu.bme.mit.theta.core.type.bvtype.BvSExtExpr
import hu.bme.mit.theta.core.type.bvtype.BvZExtExpr
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.type.inttype.IntModExpr
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.model.XcfaBuilder
import hu.bme.mit.theta.xcfa.model.XcfaLabel
import hu.bme.mit.theta.xcfa.utils.asConstantBigInteger
import hu.bme.mit.theta.xcfa.utils.collectVarsWithAccessType
import hu.bme.mit.theta.xcfa.utils.getAllLabels
import hu.bme.mit.theta.xcfa.utils.isWritten
import java.math.BigInteger

/**
 * Which string literals a variable can hold, over all definitions in the model, and the text of
 * each literal from its initialization.
 */
internal class StringLiterals(private val xcfa: XcfaBuilder) {
  /** The sources of each definition of a variable, or null for a definition of unknown value. */
  private val definitions = mutableMapOf<VarDecl<*>, MutableList<List<VarDecl<*>>?>>()
  private val cells = mutableMapOf<VarDecl<*>, MutableMap<Int, Int>>()

  /** Constant folding replaces a literal by its base id, in values and in cell addresses. */
  private val bases = mutableMapOf<BigInteger, VarDecl<*>>()
  private val constants = mutableMapOf<VarDecl<*>, MutableSet<BigInteger>>()
  private val baseCells = mutableMapOf<BigInteger, MutableMap<Int, Int>>()

  init {
    xcfa.getProcedures().forEach { procedure ->
      procedure.getEdges().forEach { edge -> edge.label.getAllLabels().forEach(::visit) }
    }
  }

  private fun visit(label: XcfaLabel) {
    when (val stmt = (label as? StmtLabel)?.stmt) {
      is AssignStmt<*> -> {
        val constant = stmt.expr.asConstantBigInteger()
        if (constant != null && stmt.varDecl.isStringLiteral()) bases[constant] = stmt.varDecl
        if (constant != null) constants.getOrPut(stmt.varDecl) { mutableSetOf() }.add(constant)
        define(stmt.varDecl, if (constant != null) listOf() else sourcesOf(stmt.expr))
      }
      is HavocStmt<*> -> define(stmt.varDecl, null)
      is MemoryAssignStmt<*, *, *> -> {
        val literal = (stmt.deref.array as? RefExpr<*>)?.decl as? VarDecl<*>
        val base = stmt.deref.array.asConstantBigInteger()
        val index = stmt.deref.offset.asConstantBigInteger()
        val value = stmt.expr.asConstantBigInteger()
        if (index != null && value != null) {
          if (literal != null && literal.isStringLiteral()) {
            cells.getOrPut(literal) { mutableMapOf() }[index.toInt()] = value.toInt()
          }
          if (base != null)
            baseCells.getOrPut(base) { mutableMapOf() }[index.toInt()] = value.toInt()
        }
      }
      null ->
        label
          .collectVarsWithAccessType(xcfa)
          .filter { it.value.isWritten }
          .keys
          .forEach { define(it, null) }
      else -> {}
    }
  }

  private fun define(variable: VarDecl<*>, sources: List<VarDecl<*>>?) {
    definitions.getOrPut(variable) { mutableListOf() }.add(sources)
  }

  /**
   * The variables whose value [expr] is. Casts wrap the value: `(mod (+ x) 2^w)` under integer
   * arithmetic, a low `extract` and an extension under bitvector arithmetic. They keep the small
   * base id that a literal holds.
   */
  private fun sourcesOf(expr: Expr<*>): List<VarDecl<*>>? {
    return when (expr) {
      is RefExpr<*> -> listOf(expr.decl as? VarDecl<*> ?: return null)
      is IteExpr<*> ->
        (sourcesOf(expr.then) ?: return null) + (sourcesOf(expr.`else`) ?: return null)
      is IntModExpr -> if (expr.rightOp is IntLitExpr) sourcesOf(expr.leftOp) else null
      is AddExpr<*> -> if (expr.ops.size == 1) sourcesOf(expr.ops[0]) else null
      is PosExpr<*> -> sourcesOf(expr.op)
      is BvPosExpr -> sourcesOf(expr.op)
      is BvSExtExpr -> sourcesOf(expr.op)
      is BvZExtExpr -> sourcesOf(expr.op)
      is BvExtractExpr -> if (expr.from.value.signum() == 0) sourcesOf(expr.bitvec) else null
      else -> null
    }
  }

  /** Whether [expr] is the folded base id of a string literal. */
  fun isLiteralBase(expr: Expr<*>): Boolean = expr.asConstantBigInteger() in bases.keys

  /** The texts that [expr] can hold, or null if one of its values is not a known literal. */
  fun textsOf(expr: Expr<*>): List<String>? {
    val sources = sourcesOf(expr) ?: return null
    return sources.flatMap { textsOf(it) ?: return null }.ifEmpty { null }
  }

  /** The texts that [variable] can hold, or null if one of its values is not a known literal. */
  fun textsOf(variable: VarDecl<*>): List<String>? {
    val literals = literalsOf(variable, mutableSetOf()) ?: return null
    if (literals.isEmpty()) return null
    return literals.map { textOf(it) ?: return null }
  }

  private fun literalsOf(variable: VarDecl<*>, seen: MutableSet<VarDecl<*>>): Set<VarDecl<*>>? {
    if (variable.isStringLiteral()) return setOf(variable)
    if (!seen.add(variable)) return emptySet()
    val defs = definitions[variable] ?: return null
    val folded = constants[variable].orEmpty().map { bases[it] ?: return null }
    return defs.flatMapTo(folded.toMutableSet()) { sources ->
      (sources ?: return null).flatMap { literalsOf(it, seen) ?: return null }
    }
  }

  private fun textOf(literal: VarDecl<*>): String? {
    val base = bases.entries.firstOrNull { it.value == literal }?.key
    val content = cells[literal] ?: baseCells[base] ?: return null
    val text = StringBuilder()
    var i = 0
    while (true) {
      val c = content[i++] ?: return null
      if (c == 0) return text.toString()
      text.append(c.toChar())
    }
  }
}

/** The frontend names each string literal's storage `__theta_str<n>`. */
private fun VarDecl<*>.isStringLiteral() = Regex("""__theta_str\d+$""").containsMatchIn(name)
