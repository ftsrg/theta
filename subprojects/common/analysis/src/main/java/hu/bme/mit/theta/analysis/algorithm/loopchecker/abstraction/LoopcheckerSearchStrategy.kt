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

import hu.bme.mit.theta.analysis.algorithm.loopchecker.AcceptancePredicate
import hu.bme.mit.theta.analysis.algorithm.loopchecker.LDGTrace
import hu.bme.mit.theta.analysis.algorithm.loopchecker.ldg.LDG
import hu.bme.mit.theta.analysis.algorithm.loopchecker.ldg.LDGEdge
import hu.bme.mit.theta.analysis.algorithm.loopchecker.ldg.LDGNode
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.common.logging.NullLogger

typealias NodeExpander<S, A> = (LDGNode<S, A>) -> Collection<LDGEdge<S, A>>

enum class LoopcheckerSearchStrategy(private val strategy: ILoopcheckerSearchStrategy) {
  GDFS(GdfsSearchStrategy),
  NDFS(NdfsSearchStrategy),
  FULL(FullSearchStrategy);

  companion object {

    val default = GDFS
  }

  fun <S : ExprState, A : ExprAction> search(
    ldg: LDG<S, A>,
    target: AcceptancePredicate<S, A>,
    expand: NodeExpander<S, A>,
    logger: Logger = NullLogger.getInstance(),
  ): Collection<LDGTrace<S, A>> = strategy.search(ldg.initNodes, target, expand, logger)
}

interface ILoopcheckerSearchStrategy {

  fun <S : ExprState, A : ExprAction> search(
    initNodes: Collection<LDGNode<S, A>>,
    target: AcceptancePredicate<S, A>,
    expand: NodeExpander<S, A>,
    logger: Logger,
  ): Collection<LDGTrace<S, A>>
}
