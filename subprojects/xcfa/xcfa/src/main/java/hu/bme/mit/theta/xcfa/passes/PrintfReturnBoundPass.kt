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
import hu.bme.mit.theta.core.stmt.Stmts.Assume
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AddExpr
import hu.bme.mit.theta.core.type.abstracttype.PosExpr
import hu.bme.mit.theta.core.type.anytype.IteExpr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.bvtype.BvExprs
import hu.bme.mit.theta.core.type.bvtype.BvExtractExpr
import hu.bme.mit.theta.core.type.bvtype.BvPosExpr
import hu.bme.mit.theta.core.type.bvtype.BvSExtExpr
import hu.bme.mit.theta.core.type.bvtype.BvType
import hu.bme.mit.theta.core.type.bvtype.BvZExtExpr
import hu.bme.mit.theta.core.type.inttype.IntExprs
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.type.inttype.IntModExpr
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.xcfa.model.SequenceLabel
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.model.XcfaBuilder
import hu.bme.mit.theta.xcfa.model.XcfaLabel
import hu.bme.mit.theta.xcfa.model.XcfaProcedureBuilder
import hu.bme.mit.theta.xcfa.utils.asConstantBigInteger
import hu.bme.mit.theta.xcfa.utils.collectVarsWithAccessType
import hu.bme.mit.theta.xcfa.utils.getAllLabels
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import hu.bme.mit.theta.xcfa.utils.isWritten
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

  private var analysis: Literals? = null

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    val formats = builder.parent.formatArguments
    if (formats.isEmpty()) return builder
    val literals = analysis ?: Literals(builder.parent).also { analysis = it }
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

  /**
   * Which string literals a variable can hold, over all definitions in the model, and the text of
   * each literal from its initialization.
   */
  internal class Literals(xcfa: XcfaBuilder) {
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
            .collectVarsWithAccessType()
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
}

/** The frontend names each string literal's storage `__theta_str<n>`. */
private fun VarDecl<*>.isStringLiteral() = Regex("""__theta_str\d+$""").containsMatchIn(name)
