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
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.model.MutableValuation
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.type.BinaryExpr
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.abstracttype.*
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.anytype.IteExpr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.AndExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.*
import hu.bme.mit.theta.core.type.booltype.NotExpr
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.asConstantBigInteger
import hu.bme.mit.theta.xcfa.utils.getFlatLabels
import hu.bme.mit.theta.xcfa.utils.intValue
import hu.bme.mit.theta.xcfa.utils.integerOf
import java.math.BigInteger

class AmbiguousMutexPass(private val parseContext: ParseContext = ParseContext()) : ProcedurePass {

  companion object {

    // create at most this many valuations for a single havoced variable
    private val HAVOC_ENUMERATION_LIMIT = BigInteger.valueOf(100)
  }

  private lateinit var possibleLiteralValues: Map<VarDecl<*>, Set<LitExpr<*>?>>

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    // Every procedure has its own instance of this pass, but it resolves the whole model at once.
    if (builder.parent.metaData.put(PROCESSED, Unit) != null) return builder
    val procedures = builder.parent.getProcedures().toList()
    procedures.forEach { it.foldMutexAddresses() }
    val unresolved =
      procedures
        .flatMap { it.getEdges() }
        .flatMap { it.getFlatLabels() }
        .filter { it.mutexAddresses.any { address -> address !is LitExpr<*> } }
    if (unresolved.isEmpty()) return builder

    possibleLiteralValues = collectPossibleLiteralValues(builder)
    val replacements = mutableMapOf<XcfaLabel, List<List<XcfaLabel>>>()
    // Resolve the whole model before committing any literal alternatives: symbolic and literal
    // aliases must use the same encoding if even one operation needs the fallback.
    for (label in unresolved) {
      val addresses = label.mutexAddresses
      val vars = addresses.flatMap { ExprUtils.getVars(it) }.toSet()
      val valuations =
        vars
          .fold(setOf<Valuation>(ImmutableValuation.empty())) { combinations, variable ->
            combinations
              .flatMap { valuation ->
                (possibleLiteralValues[variable] ?: setOf(null)).map { value ->
                  MutableValuation.copyOf(valuation).also {
                    if (value != null) it.put(variable, value)
                  }
                }
              }
              .toSet()
          }
          .ifEmpty { setOf(ImmutableValuation.empty()) }
      val alternatives = mutableListOf<List<XcfaLabel>>()
      for (valuation in valuations) {
        val simplified = addresses.map { it.resolved(valuation) }
        if (simplified.any { it !is LitExpr<*> }) {
          return SymbolicMutexPass().runChecked(builder)
        }
        val guard = And(valuation.toMap().map { (v, value) -> Eq(v.ref, value) })
        alternatives.add(
          listOf(StmtLabel(AssumeStmt.of(guard)), label.withMutexAddresses(simplified))
        )
      }
      replacements[label] = alternatives.distinct()
    }

    for (procedure in procedures) {
      for (edge in procedure.getEdges().toList()) {
        if (edge.getFlatLabels().none { it in replacements }) continue
        procedure.removeEdge(edge)
        for (part in edge.splitIf { it in replacements }) {
          val alternatives =
            part.getFlatLabels().fold(listOf(emptyList<XcfaLabel>())) { acc, label ->
              acc.flatMap { prefix ->
                (replacements[label] ?: listOf(listOf(label))).map { prefix + it }
              }
            }
          alternatives.forEach {
            procedure.addEdge(part.withLabel(SequenceLabel(it, part.label.metadata)))
          }
        }
      }
    }

    return builder
  }

  private fun XcfaProcedureBuilder.foldMutexAddresses() {
    for (edge in getEdges().toList()) {
      if (edge.getFlatLabels().none { it.mutexAddresses.isNotEmpty() }) continue
      removeEdge(edge)
      val labels =
        edge.getFlatLabels().map { label ->
          val addresses = label.mutexAddresses
          if (addresses.isEmpty()) label
          else label.withMutexAddresses(addresses.map { it.resolved() })
        }
      addEdge(edge.withLabel(SequenceLabel(labels, edge.label.metadata)))
    }
  }

  private fun Expr<*>.resolved(valuation: Valuation = ImmutableValuation.empty()): Expr<*> =
    ExprUtils.simplify(ExprUtils.simplify(this, valuation).foldSubObjectAddresses())

  /**
   * A handle like `&s.m` or `&m[1]` reads the cell holding the subobject's base, whose value is the
   * subobject's constant address. Cells holding program pointers are not recorded.
   */
  private fun Expr<*>.foldSubObjectAddresses(): Expr<*> {
    val folded = if (ops.isEmpty()) this else map { it.foldSubObjectAddresses() }
    val deref = folded as? Dereference<*, *, *> ?: return folded
    val parent = deref.array.asConstantBigInteger() ?: return folded
    val unit = deref.offset.asConstantBigInteger() ?: return folded
    val address = parseContext.staticSubObjectAddressAt(parent, unit) ?: return folded
    return deref.type.integerOf(address) ?: folded
  }

  private fun collectPossibleLiteralValues(
    builder: XcfaProcedureBuilder
  ): Map<VarDecl<*>, Set<LitExpr<*>?>> {
    val assignments = mutableMapOf<VarDecl<*>, MutableSet<Expr<*>>>()
    val havocedVars = mutableSetOf<VarDecl<*>>()
    val interestingToProcess = mutableSetOf<VarDecl<*>>()

    data class VisitItem(
      val pendingHavocs: Set<VarDecl<*>> = emptySet(),
      val conditions: Map<VarDecl<*>, IteExpr<*>> = emptyMap(),
      val anyFence: Boolean = false,
    )

    builder.parent.getProcedures().forEach { proc ->
      // locations to visit with the set of "pending" havocs (havocs with no assumption afterwards)
      val waitlist = mutableMapOf(proc.initLoc to VisitItem())
      val visited = mutableSetOf<XcfaLocation>()
      while (waitlist.isNotEmpty()) {
        val loc = waitlist.keys.first()
        val visitItem = waitlist[loc]!!
        waitlist.remove(loc)
        val (pendingHavocs, conditions, previousFence) =
          if (loc.incomingEdges.size > 1) {
            havocedVars.addAll(visitItem.pendingHavocs)
            Triple(mutableSetOf(), mutableMapOf(), false)
          } else {
            Triple(
              visitItem.pendingHavocs.toMutableSet(),
              visitItem.conditions.toMutableMap(),
              visitItem.anyFence,
            )
          }
        if (visited.add(loc)) {
          if (loc.outgoingEdges.isEmpty() && previousFence) {
            havocedVars.addAll(pendingHavocs)
          }
          loc.outgoingEdges.forEach { edge ->
            edge.getFlatLabels().forEach { label ->
              if (label is StmtLabel) {
                when (val stmt = label.stmt) {
                  is AssignStmt<*> -> {
                    val e = stmt.expr
                    if (e is RefExpr<*> && e.decl in pendingHavocs) {
                      pendingHavocs.add(stmt.varDecl)
                    } else {
                      assignments.getOrPut(stmt.varDecl) { mutableSetOf() }.add(e)
                    }

                    if (e is IteExpr<*> && e.then is LitExpr<*> && e.`else` is LitExpr<*>) {
                      conditions[stmt.varDecl] = e
                    }
                  }

                  is HavocStmt<*> -> pendingHavocs.add(stmt.varDecl)
                  is AssumeStmt -> {
                    val (assumedVar, lowerBound, upperBound) =
                      collectAssumptionValues(stmt.cond, Assumption(), conditions, pendingHavocs)
                    if (assumedVar != null && lowerBound != null && upperBound != null) {
                      if (upperBound - lowerBound + BigInteger.ONE <= HAVOC_ENUMERATION_LIMIT) {
                        var i = lowerBound
                        while (i <= upperBound) {
                          val litExpr = assumedVar.type.integerOf(i)
                          if (litExpr != null) {
                            assignments.getOrPut(assumedVar) { mutableSetOf() }.add(litExpr)
                          }
                          i++
                        }
                        pendingHavocs.remove(assumedVar)
                      }
                    }
                  }
                }
              } else {
                label.mutexAddresses.forEach { interestingToProcess.addAll(ExprUtils.getVars(it)) }
              }
            }
            val isFence =
              previousFence || edge.getFlatLabels().any { it.mutexAddresses.isNotEmpty() }
            waitlist[edge.target] = VisitItem(pendingHavocs.toSet(), conditions.toMap(), isFence)
          }
        }
      }
    }

    val result = mutableMapOf<VarDecl<*>, MutableSet<LitExpr<*>?>>()

    val initialDependencyNodes = mutableMapOf<VarDecl<*>, DependencyNode>()

    val interestingVars = mutableSetOf<VarDecl<*>>()
    while (interestingToProcess.isNotEmpty()) {
      val v = interestingToProcess.first()
      interestingToProcess.remove(v)
      if (interestingVars.add(v)) {
        val dependencies = mutableSetOf<DependencyEdge>()
        result[v] = if (v in havocedVars) mutableSetOf(null) else mutableSetOf()
        assignments[v]?.forEach { expr ->
          val simplified = expr.resolved()
          if (simplified is LitExpr<*>) {
            result[v]!!.add(simplified)
          } else {
            val vars = ExprUtils.getVars(simplified)
            vars.forEach {
              val node = initialDependencyNodes.getOrPut(it) { DependencyNode(it) }
              dependencies.add(DependencyEdge(setOf(simplified), node))
            }
            interestingToProcess.addAll(vars.filter { it !in interestingVars })
          }
        }
        val current = initialDependencyNodes.getOrPut(v) { DependencyNode(v) }
        current.dependencies.addAll(dependencies)
      }
    }

    val addPossibleValue = { variable: VarDecl<*>, value: LitExpr<*>? ->
      result.getOrPut(variable) { mutableSetOf() }.add(value)
    }

    val addPossibleValues = { expr: Expr<*>, node: DependencyNode ->
      var changed = false
      expr.getPossibleValuations(result).forEach { valuation ->
        val simplified = expr.resolved(valuation) as? LitExpr<*>
        if (addPossibleValue(node.variable, simplified)) {
          changed = true
        }
      }
      changed
    }

    val sccs = getSCCs(initialDependencyNodes.values.toSet())
    sccs.forEach { scc ->
      // iterating in topological order (root is last)
      scc.forEach { node ->
        node.dependencies.forEach { dependency ->
          if (dependency.target !in scc) {
            // if the dependency is outside the SCC, we can use the already computed values
            dependency.exprs.forEach { expr -> addPossibleValues(expr, node) }
          }
        }
      }
      val changed = scc.toMutableSet()
      while (changed.isNotEmpty()) {
        val oldChanged = changed.toSet()
        changed.clear()
        scc.forEach { node ->
          node.dependencies.forEach { dependency ->
            if (dependency.target in oldChanged) {
              dependency.exprs.forEach { expr ->
                if (expr.supportedInSccPropagation) {
                  if (addPossibleValues(expr, node)) {
                    changed.add(node)
                  }
                } else {
                  if (addPossibleValue(node.variable, null)) {
                    changed.add(node)
                  }
                }
              }
            }
          }
        }
      }
    }

    return result
  }

  private fun Expr<*>.getPossibleValuations(
    possibleValues: Map<VarDecl<*>, Set<LitExpr<*>?>>
  ): Set<Valuation> {
    return ExprUtils.getVars(this).fold(setOf(MutableValuation())) { combinations, v ->
      combinations.flatMapTo(mutableSetOf()) { combination ->
        possibleValues[v]?.map { value ->
          MutableValuation.copyOf(combination).also { if (value != null) it.put(v, value) }
        } ?: listOf(combination)
      }
    }
  }

  private class DependencyNode(
    val variable: VarDecl<*>,
    val dependencies: MutableSet<DependencyEdge> = mutableSetOf(),
  )

  private data class DependencyEdge(val exprs: Set<Expr<*>>, val target: DependencyNode)

  /** Compute SCCs, Tarjan's algorithm. Returns SCCs in topological order (root is last). */
  private fun getSCCs(nodes: Set<DependencyNode>): List<Set<DependencyNode>> {
    val indexMap = mutableMapOf<DependencyNode, Int>()
    val lowLinkMap = mutableMapOf<DependencyNode, Int>()
    val onStack = mutableSetOf<DependencyNode>()
    val stack = mutableListOf<DependencyNode>()
    val sccs = mutableListOf<Set<DependencyNode>>()
    var index = 0

    fun strongConnect(node: DependencyNode) {
      indexMap[node] = index
      lowLinkMap[node] = index
      index++
      stack.add(node)
      onStack.add(node)

      node.dependencies.forEach { edge ->
        val target = edge.target
        if (target !in indexMap) {
          strongConnect(target)
          lowLinkMap[node] = minOf(lowLinkMap[node]!!, lowLinkMap[target]!!)
        } else if (target in onStack) {
          lowLinkMap[node] = minOf(lowLinkMap[node]!!, indexMap[target]!!)
        }
      }

      if (lowLinkMap[node] == indexMap[node]) {
        val scc = mutableSetOf<DependencyNode>()
        var w: DependencyNode
        do {
          w = stack.removeAt(stack.size - 1)
          onStack.remove(w)
          scc.add(w)
        } while (w != node)
        sccs.add(scc)
      }
    }

    nodes.forEach { node ->
      if (node !in indexMap) {
        strongConnect(node)
      }
    }

    return sccs
  }

  private val Expr<*>.supportedInSccPropagation: Boolean
    get() =
      when (this) {
        is LitExpr<*>,
        is RefExpr<*> -> true

        is PosExpr<*> -> op.supportedInSccPropagation
        is NegExpr<*> -> op.supportedInSccPropagation
        is ModExpr<*> -> leftOp.supportedInSccPropagation && rightOp.supportedInSccPropagation
        else -> false
      }

  private data class Assumption(
    val varDecl: VarDecl<*>? = null,
    val lowerBound: BigInteger? = null,
    val upperBound: BigInteger? = null,
  ) {

    fun with(
      v: VarDecl<*>,
      newLowerBound: BigInteger? = lowerBound,
      newUpperBound: BigInteger? = upperBound,
    ): Assumption =
      if (varDecl == null || varDecl == v) {
        Assumption(
          v,
          newLowerBound?.let { maxOf(lowerBound ?: it, it) } ?: lowerBound,
          newUpperBound?.let { minOf(upperBound ?: it, it) } ?: upperBound,
        )
      } else this

    fun with(
      v: VarDecl<*>,
      newLowerBound: (() -> BigInteger?)? = { lowerBound },
      newUpperBound: (() -> BigInteger?)? = { upperBound },
    ): Assumption =
      if (varDecl == null || varDecl == v) {
        with(v, newLowerBound?.let { it() }, newUpperBound?.let { it() })
      } else this
  }

  private fun collectAssumptionValues(
    cond: Expr<*>,
    assumption: Assumption,
    conditions: Map<VarDecl<*>, IteExpr<*>>,
    havocs: Set<VarDecl<*>>,
  ): Assumption =
    when (cond) {
      is EqExpr<*> -> {
        val varAndValue =
          pairOfVarAndValue(cond.leftOp, cond.rightOp)
            ?: pairOfVarAndValue(cond.rightOp, cond.leftOp)
        if (varAndValue != null) {
          val (v, value) = varAndValue
          val intVal = value.intValue
          if (v in havocs && intVal != null) {
            Assumption(v, value.intValue, value.intValue)
          } else if (v in conditions && intVal != null) {
            val ite = conditions[v]!!
            collectIteAssumptions(intVal, ite, true, assumption, conditions, havocs)
          } else assumption
        } else assumption
      }

      is NeqExpr<*> -> collectIteOnlyNeq(cond, assumption, conditions, havocs)
      is NotExpr -> {
        if (cond.op is EqExpr<*>) {
          collectIteOnlyNeq(cond.op as BinaryExpr<*, *>, assumption, conditions, havocs)
        } else assumption
      }

      is GeqExpr<*> -> getBounds(cond.leftOp, cond.rightOp, assumption, havocs, true)

      is GtExpr<*> -> getBounds(cond.leftOp, cond.rightOp, assumption, havocs, false)

      is LeqExpr<*> -> getBounds(cond.rightOp, cond.leftOp, assumption, havocs, true)

      is LtExpr<*> -> getBounds(cond.rightOp, cond.leftOp, assumption, havocs, false)

      is AndExpr ->
        cond.ops.fold(assumption) { a, op -> collectAssumptionValues(op, a, conditions, havocs) }

      else -> assumption
    }

  private fun collectIteOnlyNeq(
    cond: BinaryExpr<*, *>,
    assumption: Assumption,
    conditions: Map<VarDecl<*>, IteExpr<*>>,
    havocs: Set<VarDecl<*>>,
  ): Assumption {
    val varAndValue =
      pairOfVarAndValue(cond.leftOp, cond.rightOp) ?: pairOfVarAndValue(cond.rightOp, cond.leftOp)
    return if (varAndValue != null) {
      val (v, value) = varAndValue
      val intVal = value.intValue
      if (v in conditions && intVal != null) {
        val ite = conditions[v]!!
        collectIteAssumptions(intVal, ite, false, assumption, conditions, havocs)
      } else assumption
    } else assumption
  }

  private fun collectIteAssumptions(
    intVal: BigInteger,
    ite: IteExpr<*>,
    isThen: Boolean,
    assumption: Assumption,
    conditions: Map<VarDecl<*>, IteExpr<*>>,
    havocs: Set<VarDecl<*>>,
  ): Assumption {
    val branch = if (isThen) ite.then else ite.`else`
    return if (intVal == (branch as? LitExpr<*>)?.intValue) {
      collectAssumptionValues(ite.cond, assumption, conditions, havocs)
    } else assumption
  }

  private fun getBounds(
    upper: Expr<*>,
    lower: Expr<*>,
    assumption: Assumption,
    havocs: Set<VarDecl<*>>,
    orEqual: Boolean,
  ): Assumption {
    val corrigation = if (orEqual) BigInteger.ZERO else BigInteger.ONE
    val vnv1 = pairOfVarAndValue(upper, lower)
    if (vnv1 != null) {
      val (v, value) = vnv1
      if (v in havocs) {
        return assumption.with(v, newLowerBound = { value.intValue?.let { it + corrigation } })
      }
    } else {
      val vnv2 = pairOfVarAndValue(lower, upper)
      if (vnv2 != null) {
        val (v, value) = vnv2
        if (v in havocs) {
          return assumption.with(v, newUpperBound = { value.intValue?.let { it - corrigation } })
        }
      }
    }
    return assumption
  }

  private fun pairOfVarAndValue(ref: Expr<*>, value: Expr<*>): Pair<VarDecl<*>, LitExpr<*>>? =
    pairIfBothNotNull((ref as? RefExpr<*>)?.decl as? VarDecl<*>, value as? LitExpr<*>)

  private fun <A, B> pairIfBothNotNull(first: A?, second: B?): Pair<A, B>? =
    if (first != null && second != null) Pair(first, second) else null
}

private const val PROCESSED = "ambiguousMutexProcessed"
