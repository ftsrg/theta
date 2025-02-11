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

import hu.bme.mit.theta.analysis.PartialOrd
import hu.bme.mit.theta.analysis.State

class MultiPartialOrd<
  LState : State,
  RState : State,
  DataState : State,
  LControl : State,
  RControl : State,
  MState : MultiState<LControl, RControl, DataState>,
>(
  private val leftPartOrd: PartialOrd<LState>,
  private val leftCombineStates: (LControl, DataState) -> LState,
  private val rightPartOrd: PartialOrd<RState>,
  private val rightCombineStates: (RControl, DataState) -> RState,
) : PartialOrd<MState> {

  override fun isLeq(state1: MState, state2: MState): Boolean {
    return (leftPartOrd.isLeq(
      leftCombineStates(state1.leftState, state1.dataState),
      leftCombineStates(state2.leftState, state2.dataState),
    ) &&
      rightPartOrd.isLeq(
        rightCombineStates(state1.rightState, state1.dataState),
        rightCombineStates(state2.rightState, state2.dataState),
      ) &&
      ((!state1.isSourceMatteringInEquality && !state2.isSourceMatteringInEquality) ||
        (state1.sourceSide == state2.sourceSide)))
  }
}
