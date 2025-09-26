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
package hu.bme.mit.theta.analysis.algorithm.cegar

import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.algorithm.asg.ASG
import hu.bme.mit.theta.analysis.algorithm.asg.ASGTrace
import hu.bme.mit.theta.analysis.algorithm.loopchecker.abstraction.ASGAbstractor
import hu.bme.mit.theta.analysis.algorithm.loopchecker.refinement.SingleASGTraceRefiner
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.utils.AsgVisualizer
import hu.bme.mit.theta.common.logging.Logger
import java.util.*

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

/**
 * Counterexample-Guided Abstraction Refinement (CEGAR) loop implementation, that uses an Abstractor
 * to explore the abstract state space and a Refiner to check counterexamples and refine them if
 * needed. It also provides certain statistics about its execution.
 */
object AsgCegarChecker {
  fun <S : ExprState, A : ExprAction, P : Prec> create(
    abstractor: ASGAbstractor<S, A, P>,
    refiner: SingleASGTraceRefiner<S, A, P>,
    logger: Logger,
  ): CegarChecker<P, ASG<S, A>, ASGTrace<S, A>> {
    return CegarChecker.create(
      abstractor,
      refiner,
      logger,
      AsgVisualizer<S, A>({ o: Any? -> Objects.toString(o) }, { o: Any? -> Objects.toString(o) }),
    )
  }
}
