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

import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.c2xcfa.CMetaData
import hu.bme.mit.theta.c2xcfa.LoopHead
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.anytype.IteExpr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.AndExpr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.FalseExpr
import hu.bme.mit.theta.core.type.booltype.IffExpr
import hu.bme.mit.theta.core.type.booltype.ImplyExpr
import hu.bme.mit.theta.core.type.booltype.NotExpr
import hu.bme.mit.theta.core.type.booltype.OrExpr
import hu.bme.mit.theta.core.type.booltype.TrueExpr
import hu.bme.mit.theta.core.type.booltype.XorExpr
import hu.bme.mit.theta.core.type.bvtype.*
import hu.bme.mit.theta.core.type.inttype.*
import hu.bme.mit.theta.core.utils.BvUtils
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer
import hu.bme.mit.theta.frontend.transformation.model.types.complex.integer.CInteger
import hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleType
import hu.bme.mit.theta.xcfa.analysis.proof.LocationInvariants
import hu.bme.mit.theta.xcfa.model.InvokeLabel
import hu.bme.mit.theta.xcfa.model.StartLabel
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import hu.bme.mit.theta.xcfa.witnesses.ContentItem
import hu.bme.mit.theta.xcfa.witnesses.Format
import hu.bme.mit.theta.xcfa.witnesses.Invariant
import hu.bme.mit.theta.xcfa.witnesses.InvariantType
import hu.bme.mit.theta.xcfa.witnesses.Location
import java.io.File
import java.math.BigInteger

private const val MAX_DISJUNCTS = 32
private const val MAX_LENGTH = 8192

/**
 * Loop invariants from the states of a single-threaded, fully inlined proof. All states at the
 * locations of a [LoopHead] are joined. Each state keeps only its conjuncts over the C variables in
 * scope at the loop that [CInvariantPrinter] prints exactly; dropping conjuncts only weakens a
 * state, so the join stays an invariant. Loops whose head a pass removed are skipped.
 */
internal fun LocationInvariants.loopInvariantContent(
  inputFile: File,
  parseContext: ParseContext,
  budgetMillis: Long = 10_000,
): List<ContentItem> {
  if (parseContext.multiThreading) return emptyList()
  val hasCalls =
    partitions.keys.any { loc ->
      loc.outgoingEdges.any { edge ->
        edge.getFlatLabels().any { it is InvokeLabel || it is StartLabel }
      }
    }
  if (hasCalls) return emptyList()

  val loops = LinkedHashMap<LoopHead, MutableList<ExprState>>()
  for ((loc, states) in partitions) {
    val head = (loc.metadata as? CMetaData)?.loopHead ?: continue
    loops.getOrPut(head) { mutableListOf() } += states
  }
  val deadline = System.currentTimeMillis() + budgetMillis
  return loops.mapNotNull { (head, states) ->
    if (!head.complete || System.currentTimeMillis() > deadline) return@mapNotNull null
    loopInvariant(head, states, inputFile, parseContext)
  }
}

private fun loopInvariant(
  head: LoopHead,
  states: List<ExprState>,
  inputFile: File,
  parseContext: ParseContext,
): ContentItem? {
  val names =
    head.variablesAtGuard.entries
      .filter { (_, decl) -> CInvariantPrinter.cIntegerType(decl, parseContext) != null }
      .associate { (name, decl) -> decl to name }
  val printer = CInvariantPrinter(names, parseContext)
  val disjuncts = LinkedHashSet<List<String>>()
  for (state in states) {
    if (state.isBottom) continue
    val conjuncts = LinkedHashSet<String>()
    var infeasible = false
    for (conjunct in conjunctsOf(state.toExpr())) {
      if (!ExprUtils.getVars(conjunct).all { it in names }) continue
      for (simple in conjunctsOf(ExprUtils.simplify(conjunct))) {
        when (simple) {
          is TrueExpr -> {}
          is FalseExpr -> infeasible = true
          else -> printer.print(simple)?.let(conjuncts::add)
        }
      }
    }
    if (infeasible) continue
    // a state that constrains no printable variable allows every value
    if (conjuncts.isEmpty()) return null
    disjuncts += conjuncts.toList()
  }
  if (disjuncts.isEmpty()) return null

  fun conjunction(conjuncts: Collection<String>) = conjuncts.joinToString(" && ", "(", ")")
  // the conjuncts every state shares are implied by each of them
  val common = disjuncts.reduce { acc, next -> acc.filter { it in next } }
  val rests = disjuncts.map { conjuncts -> conjuncts.filter { it !in common } }
  val value =
    when {
      rests.any { it.isEmpty() } -> conjunction(common)
      disjuncts.size <= MAX_DISJUNCTS ->
        conjunction(common + rests.joinToString(" || ", "(", ")") { conjunction(it) })
      common.isNotEmpty() -> conjunction(common)
      else -> return null
    }.takeIf { it.length <= MAX_LENGTH }
      ?: conjunction(common).takeIf { common.isNotEmpty() && it.length <= MAX_LENGTH }
      ?: return null

  val loop = head.loop
  if (loop.lineNumberStart <= 0 || loop.colNumberStart < 0) return null
  return ContentItem(
    invariant =
      Invariant(
        type = InvariantType.LOOP_INVARIANT,
        location =
          Location(
            fileName = inputFile.name,
            line = loop.lineNumberStart,
            column = loop.colNumberStart + 1,
            function = loop.functionName?.takeIf { it.isNotEmpty() },
          ),
        value = value,
        format = Format.C_EXPRESSION,
      )
  )
}

/** The conjuncts of [expr] with nested conjunctions flattened, in order. */
private fun conjunctsOf(expr: Expr<BoolType>): List<Expr<BoolType>> =
  if (expr is AndExpr) expr.ops.flatMap(::conjunctsOf) else listOf(expr)

/**
 * Prints a Theta expression as a C expression with the same value, or null if it cannot do so
 * exactly. Integers are evaluated in `long long` and bounded, so the C evaluation cannot overflow.
 * Bitvectors are evaluated as their unsigned value in `unsigned long long` and masked to their
 * width, where wraparound is defined; signed comparisons flip the sign bit.
 */
internal class CInvariantPrinter(
  private val names: Map<VarDecl<*>, String>,
  private val parseContext: ParseContext,
) {

  companion object {
    private val LLONG_MIN = BigInteger.valueOf(Long.MIN_VALUE)
    private val LLONG_MAX = BigInteger.valueOf(Long.MAX_VALUE)

    /**
     * The C integer type the frontend gave [decl], unless it is a pointer or wider than 64 bits.
     */
    fun cIntegerType(decl: VarDecl<*>, parseContext: ParseContext): CInteger? {
      // not CComplexType.getType: without metadata it guesses a type from the Theta type
      val type =
        when (val cType = parseContext.metadata.getMetadataValue(decl.ref, "cType").orElse(null)) {
          is CComplexType -> cType
          is CSimpleType -> cType.actualType
          else -> null
        }
      return (type as? CInteger)?.takeIf { it !is CPointer && it.width() in 1..64 }
    }

    private fun mask(width: Int): String = BigInteger.ONE.shiftLeft(width).dec().toString() + "ULL"

    private fun signBit(width: Int): String = BigInteger.ONE.shiftLeft(width - 1).toString() + "ULL"
  }

  private class IntTerm(val text: String, val min: BigInteger, val max: BigInteger)

  fun print(expr: Expr<BoolType>): String? = bool(expr)

  private fun bool(e: Expr<*>): String? =
    when (e) {
      is TrueExpr -> "1"
      is FalseExpr -> "0"
      is NotExpr -> bool(e.op)?.let { "!$it" }
      is AndExpr -> nary(e.ops, " && ", "1")
      is OrExpr -> nary(e.ops, " || ", "0")
      is ImplyExpr -> bool(e.leftOp)?.let { l -> bool(e.rightOp)?.let { r -> "(!$l || $r)" } }
      is IffExpr -> bool(e.leftOp)?.let { l -> bool(e.rightOp)?.let { r -> "(!$l == !$r)" } }
      is XorExpr -> bool(e.leftOp)?.let { l -> bool(e.rightOp)?.let { r -> "(!$l != !$r)" } }
      is IteExpr<*> -> if (e.type is BoolType) ite(e.cond, bool(e.then), bool(e.`else`)) else null
      is IntEqExpr -> intCompare(e.leftOp, "==", e.rightOp)
      is IntNeqExpr -> intCompare(e.leftOp, "!=", e.rightOp)
      is IntLtExpr -> intCompare(e.leftOp, "<", e.rightOp)
      is IntLeqExpr -> intCompare(e.leftOp, "<=", e.rightOp)
      is IntGtExpr -> intCompare(e.leftOp, ">", e.rightOp)
      is IntGeqExpr -> intCompare(e.leftOp, ">=", e.rightOp)
      is BvEqExpr -> bvCompare(e.leftOp, "==", e.rightOp)
      is BvNeqExpr -> bvCompare(e.leftOp, "!=", e.rightOp)
      is BvULtExpr -> bvCompare(e.leftOp, "<", e.rightOp)
      is BvULeqExpr -> bvCompare(e.leftOp, "<=", e.rightOp)
      is BvUGtExpr -> bvCompare(e.leftOp, ">", e.rightOp)
      is BvUGeqExpr -> bvCompare(e.leftOp, ">=", e.rightOp)
      is BvSLtExpr -> bvCompare(e.leftOp, "<", e.rightOp, signed = true)
      is BvSLeqExpr -> bvCompare(e.leftOp, "<=", e.rightOp, signed = true)
      is BvSGtExpr -> bvCompare(e.leftOp, ">", e.rightOp, signed = true)
      is BvSGeqExpr -> bvCompare(e.leftOp, ">=", e.rightOp, signed = true)
      else -> null
    }

  private fun nary(ops: List<Expr<*>>, separator: String, empty: String): String? {
    if (ops.isEmpty()) return empty
    val printed = ops.map { bool(it) ?: return null }
    return printed.joinToString(separator, "(", ")")
  }

  private fun ite(cond: Expr<*>, then: String?, otherwise: String?): String? =
    bool(cond)?.let { c -> then?.let { t -> otherwise?.let { o -> "($c ? $t : $o)" } } }

  private fun intCompare(left: Expr<*>, op: String, right: Expr<*>): String? {
    val l = int(left) ?: return null
    val r = int(right) ?: return null
    return "(${l.text} $op ${r.text})"
  }

  /** A `long long` term, or null if a value on the way may leave the range of `long long`. */
  private fun intTerm(text: String, min: BigInteger, max: BigInteger): IntTerm? =
    if (min >= LLONG_MIN && max <= LLONG_MAX) IntTerm(text, min, max) else null

  private fun int(e: Expr<*>): IntTerm? =
    when (e) {
      is IntLitExpr -> {
        val v = e.value
        val text =
          if (v == LLONG_MIN) "(-9223372036854775807LL - 1)"
          else if (v.signum() < 0) "(${v}LL)" else "${v}LL"
        intTerm(text, v, v)
      }
      is RefExpr<*> -> {
        val decl = e.decl as? VarDecl<*> ?: return null
        val name = names[decl] ?: return null
        val type = cIntegerType(decl, parseContext) ?: return null
        val width = type.width()
        val (min, max) =
          if (type.isSsigned)
            BigInteger.ONE.shiftLeft(width - 1).negate() to
              BigInteger.ONE.shiftLeft(width - 1).dec()
          else BigInteger.ZERO to BigInteger.ONE.shiftLeft(width).dec()
        intTerm("((long long)$name)", min, max)
      }
      is IntPosExpr -> int(e.op)
      is IntNegExpr -> int(e.op)?.let { intTerm("(-${it.text})", it.max.negate(), it.min.negate()) }
      is IntAddExpr ->
        e.ops.map { int(it) ?: return null }.reduceOrNull { a, b -> add(a, b) ?: return null }
      is IntSubExpr -> {
        val l = int(e.leftOp) ?: return null
        val r = int(e.rightOp) ?: return null
        intTerm("(${l.text} - ${r.text})", l.min - r.max, l.max - r.min)
      }
      is IntMulExpr ->
        e.ops.map { int(it) ?: return null }.reduceOrNull { a, b -> mul(a, b) ?: return null }
      is IteExpr<*> -> {
        val c = bool(e.cond) ?: return null
        val t = int(e.then) ?: return null
        val o = int(e.`else`) ?: return null
        intTerm("($c ? ${t.text} : ${o.text})", t.min.min(o.min), t.max.max(o.max))
      }
      else -> null
    }

  private fun add(a: IntTerm, b: IntTerm) =
    intTerm("(${a.text} + ${b.text})", a.min + b.min, a.max + b.max)

  private fun mul(a: IntTerm, b: IntTerm): IntTerm? {
    val products = listOf(a.min * b.min, a.min * b.max, a.max * b.min, a.max * b.max)
    return intTerm("(${a.text} * ${b.text})", products.min(), products.max())
  }

  private fun bvCompare(
    left: Expr<*>,
    op: String,
    right: Expr<*>,
    signed: Boolean = false,
  ): String? {
    val width = (left.type as BvType).size
    val l = bv(left) ?: return null
    val r = bv(right) ?: return null
    return if (signed) "(($l ^ ${signBit(width)}) $op ($r ^ ${signBit(width)}))" else "($l $op $r)"
  }

  /** An `unsigned long long` expression whose value is the unsigned value of [e]. */
  private fun bv(e: Expr<*>): String? {
    val width = (e.type as? BvType)?.size ?: return null
    if (width !in 1..64) return null
    fun masked(text: String) = if (width == 64) text else "($text & ${mask(width)})"
    return when (e) {
      is BvLitExpr -> "${BvUtils.unsignedBvLitExprToBigInteger(e)}ULL"
      is RefExpr<*> -> {
        val decl = e.decl as? VarDecl<*> ?: return null
        val name = names[decl] ?: return null
        val type = cIntegerType(decl, parseContext) ?: return null
        if (type.width() != width) return null
        if (!type.isSsigned || width == 64) "((unsigned long long)$name)"
        else {
          val unsigned =
            when (width) {
              8 -> "unsigned char"
              16 -> "unsigned short"
              32 -> "unsigned int"
              else -> return null
            }
          "((unsigned long long)($unsigned)$name)"
        }
      }
      is BvPosExpr -> bv(e.op)
      is BvSignChangeExpr -> bv(e.op)
      is BvZExtExpr -> bv(e.op)
      is BvSExtExpr -> {
        val from = e.op.type.size
        val a = bv(e.op) ?: return null
        masked("((($a ^ ${signBit(from)}) - ${signBit(from)}))")
      }
      is BvExtractExpr -> {
        val a = bv(e.bitvec) ?: return null
        val from = e.from.value.toInt()
        masked(if (from == 0) a else "($a >> $from)")
      }
      is BvConcatExpr ->
        e.ops
          .map { (bv(it) ?: return null) to (it.type as BvType).size }
          .reduceOrNull { (acc, _), (next, nextWidth) ->
            "(($acc << $nextWidth) | $next)" to nextWidth
          }
          ?.first
      is BvAddExpr -> bvNary(e.ops, " + ")?.let(::masked)
      is BvMulExpr -> bvNary(e.ops, " * ")?.let(::masked)
      is BvSubExpr -> {
        val l = bv(e.leftOp) ?: return null
        val r = bv(e.rightOp) ?: return null
        masked("($l - $r)")
      }
      is BvNegExpr -> bv(e.op)?.let { masked("(0ULL - $it)") }
      is BvNotExpr -> bv(e.op)?.let { masked("(~$it)") }
      is BvAndExpr -> bvNary(e.ops, " & ")
      is BvOrExpr -> bvNary(e.ops, " | ")
      is BvXorExpr -> bvNary(e.ops, " ^ ")
      // shifting by the width or more is undefined in C, but zero in SMT
      is BvShiftLeftExpr -> {
        val a = bv(e.leftOp) ?: return null
        val b = bv(e.rightOp) ?: return null
        "($b < ${width}ULL ? ${masked("($a << $b)")} : 0ULL)"
      }
      is BvLogicShiftRightExpr -> {
        val a = bv(e.leftOp) ?: return null
        val b = bv(e.rightOp) ?: return null
        "($b < ${width}ULL ? ($a >> $b) : 0ULL)"
      }
      // division by zero is undefined in C, but defined in SMT
      is BvUDivExpr -> {
        val a = bv(e.leftOp) ?: return null
        val b = bv(e.rightOp) ?: return null
        "($b == 0ULL ? ${mask(width)} : ($a / $b))"
      }
      is BvURemExpr -> {
        val a = bv(e.leftOp) ?: return null
        val b = bv(e.rightOp) ?: return null
        "($b == 0ULL ? $a : ($a % $b))"
      }
      is IteExpr<*> -> {
        val c = bool(e.cond) ?: return null
        val t = bv(e.then) ?: return null
        val o = bv(e.`else`) ?: return null
        "($c ? $t : $o)"
      }
      else -> null
    }
  }

  private fun bvNary(ops: List<Expr<*>>, separator: String): String? =
    if (ops.isEmpty()) null else ops.map { bv(it) ?: return null }.joinToString(separator, "(", ")")
}
