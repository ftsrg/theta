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

import hu.bme.mit.theta.analysis.Action
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.analysis.TransFunc

class MultiTransFunc<
  LState : State,
  RState : State,
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
  private val defineNextSide: (MState) -> MultiSide,
  private val createState: (LControl, RControl, DataState, MultiSide) -> MState,
  private val leftTransFunc: TransFunc<LState, in LAction, in LPrec>,
  private val leftCombineStates: (LControl, DataState) -> LState,
  private val leftExtractControlState: (LState) -> LControl,
  private val leftExtractDataState: (LState) -> DataState,
  private val rightTransFunc: TransFunc<RState, in RAction, in RPrec>,
  private val rightCombineStates: (RControl, DataState) -> RState,
  private val rightExtractControlState: (RState) -> RControl,
  private val rightExtractDataState: (RState) -> DataState,
) : TransFunc<MState, MAction, MultiPrec<LPrec, RPrec, DataPrec>> {

  override fun getSuccStates(
    state: MState,
    action: MAction,
    prec: MultiPrec<LPrec, RPrec, DataPrec>?,
  ): MutableCollection<out MState> {
    val nextSide: MultiSide = defineNextSide(state)
    val succStates: MutableList<MState> = mutableListOf()
    if (nextSide != MultiSide.RIGHT && action.leftAction != null) {
      leftTransFunc
        .getSuccStates(
          leftCombineStates(state.leftState, state.dataState),
          action.leftAction,
          prec!!.leftPrec,
        )
        .map {
          createState(
            leftExtractControlState(it!!),
            state.rightState,
            leftExtractDataState(it),
            MultiSide.LEFT,
          )
        }
        .forEach(succStates::add)
    }
    if (nextSide != MultiSide.LEFT && action.rightAction != null) {
      rightTransFunc
        .getSuccStates(
          rightCombineStates(state.rightState, state.dataState),
          action.rightAction,
          prec!!.rightPrec,
        )
        .map {
          createState(
            state.leftState,
            rightExtractControlState(it!!),
            rightExtractDataState(it),
            MultiSide.RIGHT,
          )
        }
        .forEach(succStates::add)
    }
    return succStates
  }
}
