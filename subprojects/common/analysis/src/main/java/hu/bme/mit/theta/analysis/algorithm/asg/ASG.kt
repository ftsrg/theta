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
package hu.bme.mit.theta.analysis.algorithm.asg

import hu.bme.mit.theta.analysis.algorithm.Proof
import hu.bme.mit.theta.analysis.algorithm.loopchecker.AcceptancePredicate
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.expr.ExprState

/** Abstract state graph */
class ASG<S : ExprState, A : ExprAction>(
  private val acceptancePredicate: AcceptancePredicate<in S, in A>
) : Proof {

  val nodes: MutableMap<S, ASGNode<S, A>> = mutableMapOf()
  val initNodes: MutableList<ASGNode<S, A>> = mutableListOf()
  var traces: List<ASGTrace<S, A>> = emptyList()

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

  fun getOrCreateNode(state: S): ASGNode<S, A> =
    nodes.computeIfAbsent(state) { s -> ASGNode(s, acceptancePredicate.test(Pair(s, null))) }

  fun containsNode(state: S) = nodes.containsKey(state)

  fun drawEdge(
    source: ASGNode<S, A>,
    target: ASGNode<S, A>,
    action: A?,
    accepting: Boolean,
  ): ASGEdge<S, A> {
    val edge = ASGEdge(source, target, action, accepting)
    source.addOutEdge(edge)
    target.addInEdge(edge)
    return edge
  }
}

data class ASGEdge<S : ExprState, A : ExprAction>(
  val source: ASGNode<S, A>?,
  val target: ASGNode<S, A>,
  val action: A?,
  val accepting: Boolean,
)

class ASGNode<S : ExprState, A : ExprAction>(val state: S, val accepting: Boolean) {
  companion object {

    var idCounter: Long = 0
  }

  val inEdges: MutableList<ASGEdge<S, A>> = mutableListOf()
  val outEdges: MutableList<ASGEdge<S, A>> = mutableListOf()
  val id = idCounter++
  var validLoopHondas: MutableSet<ASGNode<S, A>> = hashSetOf()
  var expanded: Boolean = false
    set(value) {
      require(value) { "Can't set expanded to false" }
      field = true
    }

  fun addInEdge(edge: ASGEdge<S, A>) = inEdges.add(edge)

  fun addOutEdge(edge: ASGEdge<S, A>) = outEdges.add(edge)
}
