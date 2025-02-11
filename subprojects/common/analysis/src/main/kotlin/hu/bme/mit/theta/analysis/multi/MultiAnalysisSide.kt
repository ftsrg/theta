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
package hu.bme.mit.theta.analysis.multi

import hu.bme.mit.theta.analysis.*

data class MultiAnalysisSide<
  S : State,
  DataS : State,
  ControlS : State,
  A : Action,
  P : Prec,
  ControlP : Prec,
>(
  val analysis: Analysis<S, in A, in P>,
  val controlInitFunc: InitFunc<ControlS, ControlP>,
  val combineStates: (ControlS, DataS) -> S,
  val extractControlState: (S) -> ControlS,
  val extractDataState: (S) -> DataS,
  val extractControlPrec: (P) -> ControlP,
)
