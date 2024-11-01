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
package hu.bme.mit.theta.analysis.algorithm.loopchecker.abstraction

import hu.bme.mit.theta.analysis.Analysis
import hu.bme.mit.theta.analysis.LTS
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.algorithm.cegar.Abstractor
import hu.bme.mit.theta.analysis.algorithm.cegar.AbstractorResult
import hu.bme.mit.theta.analysis.algorithm.loopchecker.AcceptancePredicate
import hu.bme.mit.theta.analysis.algorithm.loopchecker.ldg.LDG
import hu.bme.mit.theta.analysis.algorithm.loopchecker.ldg.LDGEdge
import hu.bme.mit.theta.analysis.algorithm.loopchecker.ldg.LDGNode
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.common.logging.Logger

class LDGAbstractor<S : ExprState, A : ExprAction, P : Prec>(
  private val analysis: Analysis<S, in A, in P>,
  private val lts: LTS<in S, A>,
  private val acceptancePredicate: AcceptancePredicate<S, A>,
  private val searchStrategy: LoopcheckerSearchStrategy,
  private val logger: Logger,
) : Abstractor<P, LDG<S, A>> {

  override fun createProof() = LDG(acceptancePredicate)

  override fun check(ldg: LDG<S, A>, prec: P): AbstractorResult {
    if (ldg.isUninitialised()) {
      ldg.initialise(analysis.initFunc.getInitStates(prec))
      ldg.traces = emptyList()
    }
    val expander: NodeExpander<S, A> =
      fun(node: LDGNode<S, A>): Collection<LDGEdge<S, A>> {
        if (node.expanded) {
          return node.outEdges
        }
        node.expanded = true
        return lts.getEnabledActionsFor(node.state).flatMap { action ->
          analysis.transFunc.getSuccStates(node.state, action, prec).map(ldg::getOrCreateNode).map {
            ldg.drawEdge(node, it, action, acceptancePredicate.test(Pair(it.state, action)))
          }
        }
      }
    val searchResult = searchStrategy.search(ldg, acceptancePredicate, expander, logger)
    ldg.traces = searchResult.toList()
    return AbstractorResult(searchResult.isEmpty())
  }
}
