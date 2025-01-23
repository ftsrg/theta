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
package hu.bme.mit.theta.analysis.multi.builder

import hu.bme.mit.theta.analysis.InitFunc
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.analysis.multi.MultiPrec
import hu.bme.mit.theta.analysis.multi.MultiState
import hu.bme.mit.theta.analysis.unit.UnitPrec
import hu.bme.mit.theta.analysis.unit.UnitState

/**
 * Serves as a control initial function for a multi analysis if the product is nested and this
 * analysis is going to be a part of a larger product.
 */
internal class MultiControlInitFunc<
  LControl : State,
  RControl : State,
  LControlPrec : Prec,
  RControlPrec : Prec,
  MState : MultiState<LControl, RControl, UnitState>,
  MPrec : MultiPrec<LControlPrec, RControlPrec, UnitPrec>,
>(
  private val leftControlInitFunc: InitFunc<LControl, LControlPrec>,
  private val rightControlInitFunc: InitFunc<RControl, RControlPrec>,
  private val createState: (lState: LControl, rState: RControl) -> MState,
) : InitFunc<MState, MPrec> {

  override fun getInitStates(prec: MPrec): MutableCollection<out MState> {
    val leftInitStates: Collection<LControl> =
      HashSet(leftControlInitFunc.getInitStates(prec.leftPrec))
    val rightInitStates: Collection<RControl> =
      HashSet(rightControlInitFunc.getInitStates(prec.rightPrec))
    return leftInitStates
      .flatMap { left -> rightInitStates.map { right -> createState(left, right) } }
      .toMutableSet()
  }
}
