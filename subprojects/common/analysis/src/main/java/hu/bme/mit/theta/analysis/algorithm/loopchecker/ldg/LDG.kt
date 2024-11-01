/*
 *  Copyright 2024 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.analysis.algorithm.loopchecker.ldg

import hu.bme.mit.theta.analysis.algorithm.Proof
import hu.bme.mit.theta.analysis.algorithm.loopchecker.AcceptancePredicate
import hu.bme.mit.theta.analysis.algorithm.loopchecker.LDGTrace
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.expr.ExprState

class LDG<S : ExprState, A : ExprAction>(
  private val acceptancePredicate: AcceptancePredicate<in S, in A>
) : Proof {

  val nodes: MutableMap<S, LDGNode<S, A>> = mutableMapOf()
  val initNodes: MutableList<LDGNode<S, A>> = mutableListOf()
  var traces: List<LDGTrace<S, A>> = emptyList()

  fun isUninitialised() = initNodes.isEmpty()

  fun pruneAll() {
    initNodes.clear()
    nodes.clear()
    traces = emptyList()
  }

  fun initialise(initStates: Collection<S>) {
    check(initStates.isNotEmpty())
    initNodes.addAll(initStates.map(this::getOrCreateNode))
  }

  fun getOrCreateNode(state: S): LDGNode<S, A> =
    nodes.computeIfAbsent(state) { s -> LDGNode(s, acceptancePredicate.test(Pair(s, null))) }

  fun containsNode(state: S) = nodes.containsKey(state)

  fun drawEdge(
    source: LDGNode<S, A>,
    target: LDGNode<S, A>,
    action: A?,
    accepting: Boolean,
  ): LDGEdge<S, A> {
    val edge = LDGEdge(source, target, action, accepting)
    source.addOutEdge(edge)
    target.addInEdge(edge)
    return edge
  }
}

data class LDGEdge<S : ExprState, A : ExprAction>(
  val source: LDGNode<S, A>?,
  val target: LDGNode<S, A>,
  val action: A?,
  val accepting: Boolean,
)

class LDGNode<S : ExprState, A : ExprAction>(val state: S, val accepting: Boolean) {
  companion object {

    var idCounter: Long = 0
  }

  val inEdges: MutableList<LDGEdge<S, A>> = mutableListOf()
  val outEdges: MutableList<LDGEdge<S, A>> = mutableListOf()
  val id = idCounter++
  var validLoopHondas: MutableSet<LDGNode<S, A>> = hashSetOf()
  var expanded: Boolean = false
    set(value) {
      if (!value) {
        throw IllegalArgumentException("Can't set expanded to false")
      }
      field = true
    }

  fun addInEdge(edge: LDGEdge<S, A>) = inEdges.add(edge)

  fun addOutEdge(edge: LDGEdge<S, A>) = outEdges.add(edge)

  fun smallerEdgeCollection() = if (inEdges.size > outEdges.size) inEdges else outEdges
}
