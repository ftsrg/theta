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
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.stmt.Stmts.Assume
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.bvtype.BvExprs
import hu.bme.mit.theta.core.type.bvtype.BvType
import hu.bme.mit.theta.core.type.inttype.IntExprs
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.xcfa.model.SequenceLabel
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.model.XcfaLabel
import hu.bme.mit.theta.xcfa.model.XcfaProcedureBuilder
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import java.math.BigInteger

/**
 * Bounds the return value of a stubbed `*printf` call ([XcfaBuilder.formatArguments]) by the
 * longest text that its format can produce. Every definition of the format variable must give a
 * string literal, and every conversion must have a bound. Otherwise the return stays unbounded.
 *
 * The bound is not exact, so the variable stays in [XcfaBuilder.overApproximatedVars]. Its interval
 * there shrinks to the bound, because the real value satisfies the bound too.
 *
 * Runs after inlining, where the format variable is assigned the literal of the call site, and
 * before [StringLiteralInitPass], which can drop the initialization of the literal.
 */
class PrintfReturnBoundPass(val parseContext: ParseContext) : ProcedurePass {

  private var analysis: StringLiterals? = null

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    val formats = builder.parent.formatArguments
    if (formats.isEmpty()) return builder
    val literals = analysis ?: StringLiterals(builder.parent).also { analysis = it }
    for (edge in ArrayList(builder.getEdges())) {
      val labels = edge.getFlatLabels()
      val bounded =
        labels.flatMap { label ->
          val havoced = ((label as? StmtLabel)?.stmt as? HavocStmt<*>)?.varDecl
          val format = havoced?.let { formats[it] }
          val texts = format?.let { literals.textsOf(it) }
          val bound = texts?.map { maxFormattedLength(it) ?: return@flatMap listOf(label) }?.max()
          if (havoced == null || bound == null) listOf(label)
          else listOfNotNull(label, boundLabel(builder, havoced, bound, label))
        }
      if (bounded.size != labels.size) {
        builder.removeEdge(edge)
        builder.addEdge(edge.withLabel(SequenceLabel(bounded, edge.label.metadata)))
      }
    }
    return builder
  }

  /** `lo <= ret && ret <= bound` under integer arithmetic, `ret <= bound` (signed) otherwise. */
  private fun boundLabel(
    builder: XcfaProcedureBuilder,
    ret: VarDecl<*>,
    bound: Long,
    havoc: XcfaLabel,
  ): XcfaLabel? {
    val limit = CComplexType.getType(ret.ref, parseContext).getValue("$bound")
    val interval = builder.overApproximatedVars[ret]
    val cond: Expr<BoolType> =
      when (ret.type) {
        is IntType -> {
          val upper = IntExprs.Leq(ret.ref as Expr<IntType>, limit as Expr<IntType>)
          if (interval == null) upper
          else And(IntExprs.Geq(ret.ref as Expr<IntType>, IntExprs.Int(interval.start)), upper)
        }
        is BvType -> BvExprs.SLeq(ret.ref as Expr<BvType>, limit as Expr<BvType>)
        else -> return null
      }
    if (interval != null) {
      builder.overApproximatedVars[ret] =
        interval.start..interval.endInclusive.min(BigInteger.valueOf(bound))
    }
    return StmtLabel(Assume(cond), metadata = havoc.metadata)
  }

  /**
   * The longest text that [format] produces, or null if a conversion has no bound. Integer widths
   * come from the architecture of [parseContext].
   */
  internal fun maxFormattedLength(format: String): Long? {
    val longBits = CComplexType.getSignedLong(parseContext).width()
    val sizeBits = CComplexType.getUnsignedLong(parseContext).width()
    var total = 0L
    var i = 0
    while (i < format.length) {
      if (format[i] != '%') {
        total++
        i++
        continue
      }
      i++
      if (i < format.length && format[i] == '%') {
        total++
        i++
        continue
      }
      var alternate = false
      while (i < format.length && format[i] in "-+ #0") alternate = alternate || format[i++] == '#'
      val width = number(format, i) ?: return null
      i = width.second
      var precision: Long? = null
      if (i < format.length && format[i] == '.') {
        val p = number(format, i + 1) ?: return null
        precision = p.first
        i = p.second
      }
      var bits = 32
      var wide = false
      when {
        format.startsWith("hh", i) -> bits = 8.also { i += 2 }
        format.startsWith("ll", i) -> bits = 64.also { i += 2 }
        i < format.length && format[i] == 'h' -> bits = 16.also { i++ }
        i < format.length && format[i] == 'l' -> bits = longBits.also { i++ }.also { wide = true }
        i < format.length && format[i] == 'j' -> bits = 64.also { i++ }
        i < format.length && format[i] in "zt" -> bits = sizeBits.also { i++ }
      }
      if (i >= format.length) return null
      val digits =
        when (format[i++]) {
          'd',
          'i' -> maxOf(precision ?: 0, digitsOf(BigInteger.TWO.pow(bits - 1), 10)) + 1
          'u' -> maxOf(precision ?: 0, digitsOf(BigInteger.TWO.pow(bits).dec(), 10))
          'o' -> maxOf(precision ?: 0, digitsOf(BigInteger.TWO.pow(bits).dec(), 8)) + 1
          'x',
          'X' ->
            maxOf(precision ?: 0, digitsOf(BigInteger.TWO.pow(bits).dec(), 16)) +
              (if (alternate) 2 else 0)
          'c' -> if (wide) return null else 1
          's' -> if (wide) return null else precision ?: return null
          'p' -> 2 + digitsOf(BigInteger.TWO.pow(sizeBits).dec(), 16)
          else -> return null
        }
      total += maxOf(width.first, digits)
    }
    return total
  }

  /** The decimal number at [from] (0 if there is none) and the index after it; null for `*`. */
  private fun number(format: String, from: Int): Pair<Long, Int>? {
    if (from < format.length && format[from] == '*') return null
    var i = from
    var value = 0L
    while (i < format.length && format[i].isDigit()) {
      value = value * 10 + (format[i++] - '0')
      if (value > Int.MAX_VALUE) return null
    }
    return value to i
  }

  private fun digitsOf(value: BigInteger, radix: Int) = value.toString(radix).length.toLong()
}
