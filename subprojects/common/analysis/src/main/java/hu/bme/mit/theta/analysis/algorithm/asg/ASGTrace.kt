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

import hu.bme.mit.theta.analysis.Cex
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.common.logging.Logger.Level

class ASGTrace<S : ExprState, A : ExprAction>(
  val tail: List<ASGEdge<S, A>>,
  val honda: ASGNode<S, A>,
  val loop: List<ASGEdge<S, A>>,
) : Cex {

  val edges by lazy { tail + loop }

  constructor(
    edges: List<ASGEdge<S, A>>,
    honda: ASGNode<S, A>,
  ) : this(edges.takeWhile { it.source != honda }, honda, edges.dropWhile { it.source != honda })

  init {
    check((1 until tail.size).none { tail[it - 1].target != tail[it].source }) {
      "The edges of the tail have to connect into each other"
    }
    check(tail.isEmpty() || tail.last().target == honda) { "The tail has to finish in the honda" }
    check(loop.first().source == honda) { "The loop has to start in the honda" }
    check((1 until loop.size).none { loop[it - 1].target != loop[it].source }) {
      "The edges of the loop have to connect into each other"
    }
    check(loop.last().target == honda) { "The loop has to finish in the honda" }
  }

  override fun length() = edges.size

  fun getEdge(index: Int): ASGEdge<S, A> {
    check(index >= 0) { "Can't get negative indexed edge (${index})" }
    check(index < length()) { "Index out of range $index < ${length()}" }
    return if (index < tail.size) tail[index] else loop[index - tail.size]
  }

  fun getAction(index: Int) = getEdge(index).action

  fun getState(index: Int) = if (index < length()) getEdge(index).source!!.state else honda.state

  fun toTrace(): Trace<S, A> =
    Trace.of(edges.map { it.source!!.state } + honda.state, edges.map { it.action!! })

  fun print(logger: Logger, level: Level) {
    tail.forEach {
      logger.write(
        level,
        "%s%n---through action:---%n%s%n--------->%n",
        it.source?.state,
        it.action,
      )
    }
    logger.write(level, "---HONDA:---%n{ %s }---------%n", honda.state)
    loop.forEach {
      logger.write(level, "---through action:---%n%s%n--------->%n%s%n", it.action, it.target.state)
    }
  }
}
