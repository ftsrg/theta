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
package hu.bme.mit.theta.analysis.algorithm.loopchecker

import hu.bme.mit.theta.analysis.algorithm.asg.ASG
import hu.bme.mit.theta.analysis.algorithm.asg.ASGTrace
import hu.bme.mit.theta.analysis.algorithm.loopchecker.abstraction.LoopCheckerSearchStrategy
import hu.bme.mit.theta.analysis.algorithm.loopchecker.abstraction.NodeExpander
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.EnumSource

/**
 * The only lasso of the counter `0 -> 1 -> ... -> N -> 0` (accepting at N) is as long as the whole
 * state space, so a search whose call depth follows the path length overflows the stack here.
 */
class DeepLassoSearchTest {

  private data class Counter(val value: Int) : ExprState {
    override fun toExpr() = True()

    override fun isBottom() = false
  }

  private object Step : ExprAction {
    override fun toExpr() = True()

    override fun nextIndexing() = VarIndexingFactory.indexing(0)
  }

  @ParameterizedTest
  @EnumSource(LoopCheckerSearchStrategy::class)
  fun `lasso through a long counter chain is found`(strategy: LoopCheckerSearchStrategy) {
    val acceptance = AcceptancePredicate<Counter, Step>({ it?.value == N })
    val asg = ASG(acceptance)
    asg.initialise(listOf(Counter(0)))
    val expand: NodeExpander<Counter, Step> = { node ->
      if (node.expanded) {
        node.outEdges
      } else {
        node.expanded = true
        val succ =
          asg.getOrCreateNode(Counter(if (node.state.value < N) node.state.value + 1 else 0))
        listOf(asg.drawEdge(node, succ, Step, acceptance.test(Pair(succ.state, Step))))
      }
    }

    val lassos = onSmallStack { strategy.search(asg, acceptance, expand) }

    assertEquals(1, lassos.size)
    val lasso: ASGTrace<Counter, Step> = lassos.single()
    val edges = lasso.tail + lasso.loop
    assertEquals(asg.initNodes.single(), edges.first().source)
    assertTrue(edges.zipWithNext().all { (a, b) -> a.target == b.source })
    assertEquals(N + 1, lasso.loop.size)
    assertEquals(lasso.honda, lasso.loop.first().source)
    assertEquals(lasso.honda, lasso.loop.last().target)
    assertTrue(lasso.loop.any { it.target.accepting })
  }

  companion object {

    private const val N = 100_000

    /** A fixed stack keeps the test independent of the -Xss the test JVM happens to get. */
    private const val STACK_SIZE = 1L shl 20

    private fun <T> onSmallStack(block: () -> T): T {
      var result: Result<T>? = null
      val thread = Thread(null, { result = runCatching(block) }, "small-stack-search", STACK_SIZE)
      thread.start()
      thread.join()
      return result!!.getOrThrow()
    }
  }
}
