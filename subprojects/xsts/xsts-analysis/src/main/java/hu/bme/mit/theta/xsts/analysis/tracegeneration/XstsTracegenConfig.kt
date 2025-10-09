/*
 *  Copyright 2024-2025 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.xsts.analysis.tracegeneration

import hu.bme.mit.theta.analysis.Action
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.analysis.algorithm.tracegeneration.CegarTraceGenerationChecker
import hu.bme.mit.theta.analysis.algorithm.tracegeneration.summary.AbstractTraceSummary
import hu.bme.mit.theta.analysis.algorithm.tracegeneration.summary.TraceGenerationResult

class XstsTracegenConfig<S : State, A : Action, P : Prec>
private constructor(
  private val checker: CegarTraceGenerationChecker<S, A, P>,
  private val prec: P,
) {
  fun check(): TraceGenerationResult<AbstractTraceSummary<S, A>, S, A> {
    return checker.check(prec)
  }

  companion object {
    fun <S : State, A : Action, P : Prec> create(
      checker: CegarTraceGenerationChecker<S, A, P>,
      initPrec: P,
    ): XstsTracegenConfig<S, A, P> {
      return XstsTracegenConfig(checker, initPrec)
    }
  }
}
