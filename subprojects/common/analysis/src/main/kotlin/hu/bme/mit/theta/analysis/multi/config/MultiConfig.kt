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
package hu.bme.mit.theta.analysis.multi.config

import hu.bme.mit.theta.analysis.Action
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.algorithm.arg.ARG
import hu.bme.mit.theta.analysis.multi.MultiAction
import hu.bme.mit.theta.analysis.multi.MultiPrec
import hu.bme.mit.theta.analysis.multi.MultiState

class MultiConfig<
  DataState : State,
  LControl : State,
  RControl : State,
  LAction : Action,
  RAction : Action,
  LPrec : Prec,
  RPrec : Prec,
  DataPrec : Prec,
  MState : MultiState<LControl, RControl, DataState>,
  MAction : MultiAction<LAction, RAction>,
>(
  val checker:
    SafetyChecker<ARG<MState, MAction>, Trace<MState, MAction>, MultiPrec<LPrec, RPrec, DataPrec>>,
  val initPrec: MultiPrec<LPrec, RPrec, DataPrec>,
) {

  fun check(): SafetyResult<ARG<MState, MAction>, Trace<MState, MAction>> = checker.check(initPrec)
}
