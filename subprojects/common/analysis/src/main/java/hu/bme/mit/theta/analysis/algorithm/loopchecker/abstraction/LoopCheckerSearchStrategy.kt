/*
 *  Copyright 2025 Budapest University of Technology and Economics
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

import hu.bme.mit.theta.analysis.algorithm.asg.ASG
import hu.bme.mit.theta.analysis.algorithm.asg.ASGEdge
import hu.bme.mit.theta.analysis.algorithm.asg.ASGNode
import hu.bme.mit.theta.analysis.algorithm.asg.ASGTrace
import hu.bme.mit.theta.analysis.algorithm.loopchecker.AcceptancePredicate
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.common.logging.NullLogger

typealias NodeExpander<S, A> = (ASGNode<S, A>) -> Collection<ASGEdge<S, A>>

enum class LoopCheckerSearchStrategy(private val strategy: ILoopCheckerSearchStrategy) {
  GDFS(GdfsSearchStrategy),
  NDFS(NdfsSearchStrategy),
  FULL(FullSearchStrategy);

  companion object {

    val default = GDFS
  }

  fun <S : ExprState, A : ExprAction> search(
    ASG: ASG<S, A>,
    target: AcceptancePredicate<S, A>,
    expand: NodeExpander<S, A>,
    logger: Logger = NullLogger.getInstance(),
  ): Collection<ASGTrace<S, A>> = strategy.search(ASG.initNodes, target, expand, logger)
}

interface ILoopCheckerSearchStrategy {

  fun <S : ExprState, A : ExprAction> search(
    initNodes: Collection<ASGNode<S, A>>,
    target: AcceptancePredicate<S, A>,
    expand: NodeExpander<S, A>,
    logger: Logger,
  ): Collection<ASGTrace<S, A>>
}
