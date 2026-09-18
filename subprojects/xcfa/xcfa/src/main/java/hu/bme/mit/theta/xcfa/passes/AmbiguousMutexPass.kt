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
import hu.bme.mit.theta.core.model.MutableValuation
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.stmt.AssumeStmt
import hu.bme.mit.theta.core.stmt.HavocStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.abstracttype.ModExpr
import hu.bme.mit.theta.core.type.abstracttype.NegExpr
import hu.bme.mit.theta.core.type.abstracttype.PosExpr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Or
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.xcfa.model.FenceLabel
import hu.bme.mit.theta.xcfa.model.SequenceLabel
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.model.XcfaLabel
import hu.bme.mit.theta.xcfa.model.XcfaProcedureBuilder
import hu.bme.mit.theta.xcfa.utils.getFlatLabels

class AmbiguousMutexPass : ProcedurePass {

  private lateinit var possibleLiteralValues: Map<VarDecl<*>, Set<LitExpr<*>?>>

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    builder.getEdges().toSet().forEach { edge ->
      var changed = false
      val alternatives: List<List<XcfaLabel>> =
        edge.getFlatLabels().fold(mutableListOf<MutableList<XcfaLabel>>()) { accumulated, label ->
          var newAccumulated = accumulated
          if (label is FenceLabel && label.lock !is LitExpr<*>) {
            // lazy initialization of possible literal values for variables
            if (!this::possibleLiteralValues.isInitialized) {
              possibleLiteralValues = collectPossibleLiteralValues(builder)
            }

            val simplifiedAlternatives: Set<Pair<Expr<BoolType>?, Expr<*>>> =
              label.lock
                .getPossibleValuations(possibleLiteralValues)
                .map { possibleValuation: Valuation ->
                  val simplified = ExprUtils.simplify(label.lock, possibleValuation) as? LitExpr<*>
                  val guard =
                    simplified?.let {
                      And(possibleValuation.toMap().map { (v, value) -> Eq(v.ref, value) })
                    }
                  guard to (simplified ?: label.lock)
                }
                .toSet()
            val elseGuard = Not(Or(simplifiedAlternatives.mapNotNull { it.first }))
            newAccumulated =
              simplifiedAlternatives
                .flatMap { (guard, simplifiedLock) ->
                  val newLabels: List<XcfaLabel> =
                    if (simplifiedLock != label.lock) {
                      changed = true
                      listOf(StmtLabel(AssumeStmt.of(guard)), label.withLock(simplifiedLock))
                    } else {
                      listOf(StmtLabel(AssumeStmt.of(elseGuard)), label)
                    }
                  if (newAccumulated.isEmpty()) {
                    mutableListOf(newLabels.toMutableList())
                  } else {
                    newAccumulated.map { it.apply { addAll(newLabels) } }
                  }
                }
                .toMutableList()
          } else {
            newAccumulated.forEach { it.add(label) }
          }
          newAccumulated
        }
      if (changed) {
        builder.removeEdge(edge)
        alternatives.forEach { alternative ->
          builder.addEdge(edge.withLabel(SequenceLabel(alternative)))
        }
      }
    }

    return builder
  }

  private fun collectPossibleLiteralValues(builder: XcfaProcedureBuilder): Map<VarDecl<*>, Set<LitExpr<*>?>> {
    val assignments = mutableMapOf<VarDecl<*>, MutableSet<Expr<*>>>()
    val havocedVars = mutableSetOf<VarDecl<*>>()
    val interestingToProcess = mutableSetOf<VarDecl<*>>()
    builder.parent.getProcedures().forEach { proc ->
      proc.getEdges().forEach { edge ->
        edge.getFlatLabels().forEach { label ->
          if (label is StmtLabel) {
            if (label.stmt is AssignStmt<*>) {
              assignments.getOrPut(label.stmt.varDecl) { mutableSetOf() }.add(label.stmt.expr)
            } else if (label.stmt is HavocStmt<*>) {
              havocedVars.add(label.stmt.varDecl)
            }
          } else if (label is FenceLabel) {
            interestingToProcess.addAll(ExprUtils.getVars(label.lock))
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
          val simplified = ExprUtils.simplify(expr)
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
        val current = initialDependencyNodes.getOrDefault(v, DependencyNode(v))
        initialDependencyNodes[v] = current.withDependencies(dependencies)
      }
    }

    val addPossibleValue = { variable: VarDecl<*>, value: LitExpr<*>? ->
      result.getOrPut(variable) { mutableSetOf() }.add(value)
    }

    val addPossibleValues = { expr: Expr<*>, node: DependencyNode ->
      var changed = false
      expr.getPossibleValuations(result).forEach { valuation ->
        val simplified = ExprUtils.simplify(expr, valuation) as? LitExpr<*>
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
            dependency.exprs.forEach { expr ->
              addPossibleValues(expr, node)
            }
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

  private fun Expr<*>.getPossibleValuations(possibleValues: Map<VarDecl<*>, Set<LitExpr<*>?>>): Set<Valuation> {
    return ExprUtils
      .getVars(this)
      .fold(setOf(MutableValuation())) { combinations, v ->
        combinations.flatMapTo(mutableSetOf()) { combination ->
          possibleValues[v]?.map { value ->
            MutableValuation.copyOf(combination).also {
              if (value != null) it.put(v, value)
            }
          } ?: listOf(combination)
        }
      }
  }

  private data class DependencyNode(
    val variable: VarDecl<*>,
    val dependencies: Set<DependencyEdge> = setOf(),
  ) {

    fun withDependencies(dependencies: Set<DependencyEdge>): DependencyNode =
      DependencyNode(variable, this.dependencies + dependencies)
  }

  private data class DependencyEdge(
    val exprs: Set<Expr<*>>,
    val target: DependencyNode,
  )

  /**
   * Compute SCCs, Tarjan's algorithm. Returns SCCs in topological order (root is last).
   */
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
        is LitExpr<*>, is RefExpr<*> -> true
        is PosExpr<*> -> op.supportedInSccPropagation
        is NegExpr<*> -> op.supportedInSccPropagation
        is ModExpr<*> -> leftOp.supportedInSccPropagation && rightOp.supportedInSccPropagation
        else -> false
      }
}