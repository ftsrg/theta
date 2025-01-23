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

import hu.bme.mit.theta.analysis.InitFunc
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.State

class MultiInitFunc<
  DataState : State,
  LControl : State,
  RControl : State,
  LPrec : Prec,
  RPrec : Prec,
  LControlPrec : Prec,
  RControlPrec : Prec,
  DataPrec : Prec,
  MState : MultiState<LControl, RControl, DataState>,
>(
  private val createInitialState: (LControl, RControl, DataState) -> MState,
  private val dataInitFunc: InitFunc<DataState, DataPrec>,
  private val extractLeftControlPrec: (LPrec) -> LControlPrec,
  private val leftControlInitFunc: InitFunc<LControl, LControlPrec>,
  private val extractRightControlPrec: (RPrec) -> RControlPrec,
  private val rightControlInitFunc: InitFunc<RControl, RControlPrec>,
) : InitFunc<MState, MultiPrec<LPrec, RPrec, DataPrec>> {

  override fun getInitStates(
    prec: MultiPrec<LPrec, RPrec, DataPrec>?
  ): MutableCollection<out MState> {
    prec!!
    val leftInitPrec: LControlPrec = extractLeftControlPrec(prec.leftPrec)
    val rightInitPrec: RControlPrec = extractRightControlPrec(prec.rightPrec)
    val leftInitStates: Collection<LControl> =
      HashSet<LControl>(leftControlInitFunc.getInitStates(leftInitPrec))
    val rightInitStates: Collection<RControl> =
      HashSet<RControl>(rightControlInitFunc.getInitStates(rightInitPrec))
    val dataInitStates: Collection<DataState> = dataInitFunc.getInitStates(prec.dataPrec)
    return leftInitStates
      .flatMap { leftInitState ->
        rightInitStates.flatMap { rightInitState ->
          dataInitStates.map { dataInitState ->
            createInitialState(leftInitState, rightInitState, dataInitState)
          }
        }
      }
      .toMutableSet()
  }
}
