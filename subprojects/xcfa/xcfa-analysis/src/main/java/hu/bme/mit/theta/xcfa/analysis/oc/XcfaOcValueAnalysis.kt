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
package hu.bme.mit.theta.xcfa.analysis.oc

import hu.bme.mit.theta.analysis.algorithm.oc.EventType.WRITE
import hu.bme.mit.theta.core.decl.ConstDecl
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.decl.IndexedConstDecl
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.model.MutableValuation
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.abstracttype.EqExpr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.AndExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.False
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.NotExpr
import hu.bme.mit.theta.core.type.booltype.OrExpr
import hu.bme.mit.theta.core.type.bvtype.BvAndExpr
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr
import hu.bme.mit.theta.core.utils.BvUtils
import hu.bme.mit.theta.core.utils.ExprUtils
import java.math.BigInteger
import java.util.BitSet
import java.util.IdentityHashMap

/** For every event, the events strictly before it in every execution containing both. */
internal fun closePo(events: Collection<E>, pos: List<R>): Map<E, BitSet> {
  val successors = pos.groupBy({ it.from }, { it.to })
  val nodes = (events + pos.flatMap { listOf(it.from, it.to) }).toSet()
  val indegree = HashMap<E, Int>()
  pos.forEach { indegree.merge(it.to, 1, Int::plus) }
  val queue = ArrayDeque(nodes.filter { it !in indegree })
  val result = nodes.associateWith { BitSet() }
  var closed = 0
  while (queue.isNotEmpty()) {
    val e = queue.removeFirst()
    closed++
    successors[e]?.forEach { next ->
      result.getValue(next).apply {
        or(result.getValue(e))
        set(e.id)
      }
      if (indegree.merge(next, -1, Int::plus) == 0) queue.add(next)
    }
  }
  check(closed == nodes.size) { "Program order is cyclic." }
  return result
}

/** A binding of a local SSA constant, active under [guard]. A null [value] leaves it free. */
internal class LocalDefinition(val guard: Set<Expr<BoolType>>, val value: Expr<*>?)

/**
 * Removes the rf and ws candidates no sequentially consistent execution can use.
 *
 * Computes the least fixpoint of the values of every constant, so that addresses flowing through
 * locals and memory become known. Least, because po and rf are acyclic: by induction on an
 * execution's causal order, each of its values, and each rf edge it uses, is in the fixpoint. A
 * candidate is unused if the addresses cannot meet, if an event cannot execute, or if a write that
 * must execute in between overwrites it. Each of these only gets less likely as the sets grow, so
 * the iteration is monotone.
 */
internal class XcfaOcValueAnalysis(
  private val events: Collection<E>,
  private val before: Map<E, BitSet>,
  private val rfs: MutableMap<VarDecl<*>, MutableSet<R>>,
  private val wss: MutableMap<VarDecl<*>, MutableSet<R>>,
  private val definitions: Map<ConstDecl<*>, List<LocalDefinition>>,
  private val memoryGarbages: Set<ConstDecl<*>>,
  private val checksDereferences: Boolean = true,
) {

  private val eventsOf: Map<Decl<*>, List<E>> = events.groupBy { it.const }

  private val allCandidates: Map<E, List<R>> = rfs.values.flatten().groupBy { it.to }

  private val conjunctsOf = HashMap<Expr<BoolType>, Set<Expr<BoolType>>>()

  // guards are immutable and shared by the events of a path segment: keyed by identity
  private val impliedBy = IdentityHashMap<Set<Expr<BoolType>>, Set<Expr<BoolType>>>()

  private val implications =
    IdentityHashMap<Set<Expr<BoolType>>, IdentityHashMap<Set<Expr<BoolType>>, Boolean>>()

  private val certainlyEarlierWrites = HashMap<E, List<E>>()

  // RF-Some binds a read only if a candidate executes with it, see the solver encoding
  private val boundReads: Set<E> =
    allCandidates.filterValues { rels -> rels.any { implies(it.to.guard, it.from.guard) } }.keys

  private val order = (definitions.keys + eventsOf.keys).toList()

  /** Absent: no value yet. Mapped to null: any value. */
  private val values = HashMap<Decl<*>, Set<LitExpr<*>>?>()

  /**
   * The values usable as an address: without what a read of unwritten memory can return, since
   * following an indeterminate pointer is undefined and so ends the path, like following NULL. The
   * dereference checks need such an address to report it, so then these are simply [values].
   */
  private val addressValues = if (checksDereferences) values else HashMap()

  private var forAddress = false

  private val candidates: Map<E, List<R>> =
    allCandidates.mapValues { (read, rels) ->
      // a same-thread pair not ordered either way lies on exclusive paths
      rels.filter { !ordered(read, it.from) && (it.from.pid != read.pid || ordered(it.from, read)) }
    }

  private val evaluated = HashMap<Expr<*>, Set<LitExpr<*>>?>()

  private val evaluatedAddresses = HashMap<Expr<*>, Set<LitExpr<*>>?>()

  private val guardedValues = HashMap<Pair<E, Expr<*>>, Set<LitExpr<*>>?>()

  private val conditionsOf = HashMap<E, Map<ConstDecl<*>, List<Expr<BoolType>>>>()

  private val constantShapes = IdentityHashMap<Expr<*>, Any>()

  private val constantsOf = HashMap<Expr<*>, List<ConstDecl<*>>>()

  /** Prunes the candidates, and returns the conditions under which no execution can proceed. */
  fun prune(): List<Set<Expr<BoolType>>> {
    fixpoint()
    events.forEach { e ->
      e.arrayValues = e.array?.let { valuesAt(e, it) }
      e.offsetValues = e.offset?.let { valuesAt(e, it) }
    }
    wss.values.forEach { rels ->
      rels.removeIf { !alive(it.from) || !alive(it.to) || !sameAddressPossible(it.from, it.to) }
    }
    val unreachable = events.filter { !alive(it) }.map { it.guard }.toMutableList()
    for ((read, rels) in allCandidates) {
      val used = if (alive(read)) usedCandidates(read).toSet() else emptySet()
      // an unbound read may also execute without reading: only then are its candidates not exact
      if (used.isEmpty()) {
        if (read !in boundReads) continue
        unreachable.add(read.guard)
      }
      val decl = read.const.let { c -> (c as IndexedConstDecl<*>).varDecl }
      rfs.getValue(decl).removeAll(rels.filter { it !in used }.toSet())
    }
    return unreachable.distinct()
  }

  /** Whether [condition] holds in no execution, as all values it can be evaluated on falsify it. */
  fun isCertainlyFalse(condition: Expr<BoolType>): Boolean =
    inMode(false) { evaluate(condition) == FALSE }

  private fun fixpoint() {
    do {
      var changed = false
      evaluated.clear()
      evaluatedAddresses.clear()
      guardedValues.clear()
      for (decl in order) {
        changed = update(decl, false) || changed
        if (addressValues !== values) changed = update(decl, true) || changed
      }
    } while (changed)
  }

  private fun update(decl: Decl<*>, address: Boolean): Boolean {
    val new = inMode(address) { compute(decl) }
    val target = if (address) addressValues else values
    if ((if (decl in target) target[decl] else NOTHING) == new) return false
    target[decl] = new
    return true
  }

  private inline fun <T> inMode(address: Boolean, body: () -> T): T {
    val previous = forAddress
    forAddress = address
    return try {
      body()
    } finally {
      forAddress = previous
    }
  }

  private fun compute(decl: Decl<*>): Set<LitExpr<*>>? {
    var result: Set<LitExpr<*>>? = NOTHING
    definitions[decl]?.forEach { definition ->
      if (holds(definition.guard)) result = result.join(definition.value?.let { evaluate(it) })
    }
    // not conditional on the event's guard: the guard of a branch read refers to the read itself
    eventsOf[decl]?.forEach { e -> result = result.join(eventValue(e)) }
    return result?.takeIf { it.size <= MAX_VALUES }
  }

  private fun eventValue(e: E): Set<LitExpr<*>>? {
    val assignment = e.assignment
    if (e.type == WRITE) {
      val value =
        (assignment as? EqExpr<*>)?.takeIf { (it.leftOp as? RefExpr<*>)?.decl == e.const }?.rightOp
      return value?.let { evaluate(it) }
    }
    if (assignment != null || e !in boundReads) return null
    var result: Set<LitExpr<*>>? = NOTHING
    usedCandidates(e).forEach { rel ->
      if (rel.from.const !in memoryGarbages) result = result.join(valueOf(rel.from.const))
      else if (!forAddress || addressValues === values) result = null
    }
    return result
  }

  private fun usedCandidates(read: E): List<R> {
    val rels = candidates[read] ?: return emptyList()
    val possible = rels.filter { alive(it.from) && sameAddressPossible(it.from, read) }
    val covering = rels.map { it.from }.filter { ordered(it, read) && mustAlias(it, read) }
    val initialized = everyAddressWritten(read, rels)
    return possible.filter { rel ->
      val w = rel.from
      if (initialized && w.const in memoryGarbages) return@filter false
      covering.none { c ->
        c !== w && ordered(w, c) && (implies(read.guard, c.guard) || implies(w.guard, c.guard))
      }
    }
  }

  /**
   * Whether each address [read] can access is certainly written before it: no cell is unwritten.
   */
  private fun everyAddressWritten(read: E, rels: List<R>): Boolean {
    val arrays = read.array?.let { valuesAt(read, it) } ?: return false
    val offsets = read.offset?.let { valuesAt(read, it) } ?: return false
    val earlier =
      certainlyEarlierWrites.getOrPut(read) {
        rels
          .map { it.from }
          .filter {
            it.const !in memoryGarbages && ordered(it, read) && implies(read.guard, it.guard)
          }
      }
    val written =
      earlier
        .mapNotNull { w ->
          val array = w.array?.let { valuesAt(w, it) }?.singleOrNull() ?: return@mapNotNull null
          val offset = w.offset?.let { valuesAt(w, it) }?.singleOrNull() ?: return@mapNotNull null
          array to offset
        }
        .toSet()
    return arrays.all { array -> offsets.all { offset -> (array to offset) in written } }
  }

  /** Optimistic while a set is empty, so that it holds less as the sets grow. */
  private fun mustAlias(a: E, b: E): Boolean =
    a.const !in memoryGarbages &&
      b.const !in memoryGarbages &&
      sameKnownValue(a, a.array, b, b.array) &&
      sameKnownValue(a, a.offset, b, b.offset)

  private fun sameKnownValue(x: E, a: Expr<*>?, y: E, b: Expr<*>?): Boolean {
    if (a == null || b == null) return a == null && b == null
    val first = valuesAt(x, a) ?: return false
    val second = valuesAt(y, b) ?: return false
    return first.size <= 1 &&
      second.size <= 1 &&
      (first.isEmpty() || second.isEmpty() || first == second)
  }

  private fun sameAddressPossible(a: E, b: E): Boolean {
    if (a.const in memoryGarbages || b.const in memoryGarbages) return true
    return meets(a, a.array, b, b.array) && meets(a, a.offset, b, b.offset)
  }

  private fun meets(x: E, a: Expr<*>?, y: E, b: Expr<*>?): Boolean {
    if (a == null || b == null) return true
    val first = valuesAt(x, a)
    val second = valuesAt(y, b)
    return when {
      first == null -> second == null || second.isNotEmpty()
      second == null -> first.isNotEmpty()
      else -> first.any { it in second }
    }
  }

  /**
   * The values of [address] in an execution of [e]: the guard rules out those contradicting a
   * condition over the address's only constant, like the check that ends the path at NULL.
   */
  private fun valuesAt(e: E, address: Expr<*>): Set<LitExpr<*>>? =
    inMode(true) { guardedAddress(e, address) }

  private fun guardedAddress(e: E, address: Expr<*>): Set<LitExpr<*>>? =
    guardedValues.getOrPut(e to address) {
      val all = evaluate(address) ?: return@getOrPut null
      val constant =
        constantsOf.getOrPut(address) { ExprUtils.getConstants(address).toList() }.singleOrNull()
          ?: return@getOrPut all
      val conditions = conditionsOf.getOrPut(e) { singleConstantConditions(e) }[constant].orEmpty()
      if (conditions.isEmpty()) return@getOrPut all
      val domain = valueOf(constant) ?: return@getOrPut null
      try {
        domain
          .map { ImmutableValuation.builder().put(constant, it).build() }
          .filter { valuation -> conditions.all { it.eval(valuation) != False() } }
          .map { address.eval(it) as LitExpr<*> }
          .toSet()
      } catch (_: RuntimeException) {
        all
      }
    }

  private fun singleConstantConditions(e: E): Map<ConstDecl<*>, List<Expr<BoolType>>> =
    e.guard
      .flatMapTo(hashSetOf()) { conjuncts(it) }
      .mapNotNull { condition -> soleConstant(condition)?.let { it to condition } }
      .groupBy({ it.first }, { it.second })

  /** The only constant of [expr], if it has exactly one. Guards share subterms: walked as a DAG. */
  private fun soleConstant(expr: Expr<*>): ConstDecl<*>? = constantShape(expr) as? ConstDecl<*>

  private fun constantShape(expr: Expr<*>): Any =
    constantShapes.getOrPut(expr) {
      val decl = (expr as? RefExpr<*>)?.decl
      if (decl is ConstDecl<*>) return@getOrPut decl
      expr.ops.fold(NO_CONSTANT) { shape, op ->
        val other = constantShape(op)
        when {
          shape === NO_CONSTANT -> other
          other === NO_CONSTANT || other == shape -> shape
          else -> MANY_CONSTANTS
        }
      }
    }

  private fun implies(premise: Set<Expr<BoolType>>, conclusion: Set<Expr<BoolType>>): Boolean =
    implications
      .getOrPut(premise) { IdentityHashMap() }
      .getOrPut(conclusion) {
        val implied =
          impliedBy.getOrPut(premise) { premise.flatMapTo(hashSetOf()) { conjuncts(it) } }
        implied.containsAll(conclusion)
      }

  /** The conditions a guard implies. A merged path condition implies what all its paths do. */
  private fun conjuncts(guard: Expr<BoolType>): Set<Expr<BoolType>> =
    conjunctsOf.getOrPut(guard) {
      when (guard) {
        is AndExpr -> guard.ops.flatMapTo(hashSetOf()) { conjuncts(it) }
        is OrExpr ->
          guard.ops.map { conjuncts(it) }.reduce { common, ops -> common intersect ops }.toHashSet()
        is NotExpr ->
          (guard.op as? OrExpr)?.ops?.flatMapTo(hashSetOf()) { conjuncts(Not(it)) } ?: hashSetOf()
        else -> hashSetOf()
      } + guard
    }

  private fun alive(e: E) = holds(e.guard)

  private fun holds(guard: Set<Expr<BoolType>>): Boolean =
    inMode(false) {
      guard.none { condition -> evaluate(condition)?.let { it.isEmpty() || it == FALSE } ?: false }
    }

  private fun valueOf(decl: Decl<*>): Set<LitExpr<*>>? =
    when {
      decl !in eventsOf && decl !in definitions -> null
      decl in currentValues -> currentValues[decl]
      else -> NOTHING
    }

  private val currentValues
    get() = if (forAddress) addressValues else values

  private fun evaluate(expr: Expr<*>): Set<LitExpr<*>>? {
    val cache = if (forAddress && addressValues !== values) evaluatedAddresses else evaluated
    return if (expr in cache) cache[expr] else structural(expr).also { cache[expr] = it }
  }

  /**
   * A merged path condition mentions constants of the other incoming paths, and these may have no
   * value: only the disjunct of the path actually taken has to evaluate.
   */
  private fun structural(expr: Expr<*>): Set<LitExpr<*>>? =
    when (expr) {
      is OrExpr -> {
        val ops = expr.ops.map { evaluate(it) }.filter { it == null || it.isNotEmpty() }
        booleans(ops.any { it == null || True() in it }, ops.any { it == null || False() in it })
      }
      is AndExpr -> {
        val ops = expr.ops.map { evaluate(it) }
        if (ops.any { it != null && it.isEmpty() }) NOTHING
        else
          booleans(ops.all { it == null || True() in it }, ops.any { it == null || False() in it })
      }
      is NotExpr -> evaluate(expr.op)?.let { op -> booleans(False() in op, True() in op) }
      is BvAndExpr -> enumerate(expr) ?: maskedValues(expr)
      else -> enumerate(expr)
    }

  /**
   * Masking an unknown value only keeps some bits of the mask, like an index into a ring buffer.
   */
  private fun maskedValues(expr: BvAndExpr): Set<LitExpr<*>>? {
    val masks = expr.ops.firstNotNullOfOrNull { evaluate(it) } ?: return null
    val result = mutableSetOf<LitExpr<*>>()
    for (mask in masks) {
      val bits = BvUtils.neutralBvLitExprToBigInteger(mask as BvLitExpr)
      if (bits.bitCount() > MAX_MASK_BITS) return null
      var sub = bits
      while (true) {
        result.add(BvUtils.bigIntegerToNeutralBvLitExpr(sub, mask.type.size))
        if (sub.signum() == 0) break
        sub = (sub - BigInteger.ONE).and(bits)
      }
    }
    return result.takeIf { it.size <= MAX_VALUES }
  }

  private fun booleans(canBeTrue: Boolean, canBeFalse: Boolean): Set<LitExpr<*>> =
    listOfNotNull(True().takeIf { canBeTrue }, False().takeIf { canBeFalse }).toSet()

  private fun enumerate(expr: Expr<*>): Set<LitExpr<*>>? {
    val constants = constantsOf.getOrPut(expr) { ExprUtils.getConstants(expr).toList() }
    val domains = constants.map { valueOf(it) ?: return null }
    if (domains.any { it.isEmpty() }) return NOTHING
    val size = domains.fold(1L) { n, domain -> (n * domain.size).coerceAtMost(MAX_VALUES + 1L) }
    if (size > MAX_VALUES) return null
    var valuations = listOf(ImmutableValuation.empty() as Valuation)
    constants.zip(domains).forEach { (constant, domain) ->
      valuations =
        valuations.flatMap { valuation ->
          domain.map { MutableValuation.copyOf(valuation).put(constant, it) }
        }
    }
    return try {
      valuations.map { expr.eval(it) as LitExpr<*> }.toSet()
    } catch (_: RuntimeException) {
      null
    }
  }

  private fun ordered(from: E, to: E) = before.getValue(to)[from.id]

  private fun Set<LitExpr<*>>?.join(other: Set<LitExpr<*>>?): Set<LitExpr<*>>? =
    if (this == null || other == null) null else this + other

  private companion object {
    const val MAX_VALUES = 64
    const val MAX_MASK_BITS = 6
    val MANY_CONSTANTS = Any()
    val NO_CONSTANT = Any()
    val NOTHING: Set<LitExpr<*>> = emptySet()
    val FALSE: Set<LitExpr<*>> = setOf(False())
  }
}
