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
package hu.bme.mit.theta.analysis.multi.builder.stmt

import hu.bme.mit.theta.analysis.LTS
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.StmtAction
import hu.bme.mit.theta.analysis.multi.MultiAnalysisSide

class StmtMultiBuilder<
  LState : ExprState,
  LControl : ExprState,
  LAction : StmtAction,
  DataState : ExprState,
  LPrec : Prec,
  LControlPrec : Prec,
>(
  private val side: MultiAnalysisSide<LState, DataState, LControl, LAction, LPrec, LControlPrec>,
  private val lts: LTS<in LState, LAction>,
) {

  fun <
    RState : ExprState,
    RControl : ExprState,
    RAction : StmtAction,
    RPrec : Prec,
    RControlPrec : Prec,
  > addRightSide(
    side: MultiAnalysisSide<RState, DataState, RControl, RAction, RPrec, RControlPrec>,
    lts: LTS<in RState, RAction>,
  ) = StmtMultiBuilderPair(this.side, this.lts, side, lts)
}
