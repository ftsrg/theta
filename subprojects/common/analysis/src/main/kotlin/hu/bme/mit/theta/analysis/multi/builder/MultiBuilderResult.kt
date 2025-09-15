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

import hu.bme.mit.theta.analysis.Action
import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.analysis.multi.*
import hu.bme.mit.theta.analysis.unit.UnitPrec
import hu.bme.mit.theta.analysis.unit.UnitState

/**
 * TODO The following class in this file should be used, however, with IntelliJ IDEA 2024.1
 * (Ultimate Edition) Build #IU-241.14494.240, built on March 28, 2024 Kotlin: 241.14494.240-IJ the
 * usage of this class causes the kotlin plugin to crash, maybe even crashing the whole IDE. For
 * this reason, a POJO has to be used instead
 */
private data class MultiBuilderResult<
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
  LControlPrec : Prec,
  RControlPrec : Prec,
  MState : MultiState<LControl, RControl, DataState>,
  MControlState : MultiState<LControl, RControl, UnitState>,
  MAction : MultiAction<LAction, RAction>,
  MLts : MultiLts<LState, RState, DataState, LControl, RControl, LAction, RAction, MState, MAction>,
>(
  val side:
    MultiAnalysisSide<
      MState,
      DataState,
      MControlState,
      MAction,
      MultiPrec<LPrec, RPrec, DataPrec>,
      MultiPrec<LControlPrec, RControlPrec, UnitPrec>,
    >,
  val lts: MLts,
)

internal fun <
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
  LControlPrec : Prec,
  RControlPrec : Prec,
  MState : MultiState<LControl, RControl, DataState>,
  MControlState : MultiState<LControl, RControl, UnitState>,
  MAction : MultiAction<LAction, RAction>,
  MAnalysis : MultiAnalysis<
    LState,
    RState,
    DataState,
    LControl,
    RControl,
    LAction,
    RAction,
    LPrec,
    RPrec,
    DataPrec,
    LControlPrec,
    RControlPrec,
    MState,
    MControlState,
    MAction,
  >,
  MLts : MultiLts<LState, RState, DataState, LControl, RControl, LAction, RAction, MState, MAction>,
> multiBuilderResult(
  analysis: MAnalysis,
  lts: MLts,
): MultiBuilderResultPOJO<
  LState,
  RState,
  DataState,
  LControl,
  RControl,
  LAction,
  RAction,
  LPrec,
  RPrec,
  DataPrec,
  LControlPrec,
  RControlPrec,
  MState,
  MControlState,
  MAction,
  MLts,
> {
  val initFunc =
    MultiControlInitFunc(
      analysis.leftSide.controlInitFunc,
      analysis.rightSide.controlInitFunc,
      analysis::createControlInitState,
    )
  val combineStates: (MControlState, DataState) -> MState = { controlS, dataS ->
    analysis.createState(controlS.leftState, controlS.rightState, dataS, controlS.sourceSide)
  }
  val extractControlState: (MState) -> MControlState = { mState ->
    analysis.createControlState(mState.leftState, mState.rightState, mState.sourceSide)
  }
  val extractDataFromState: (MState) -> DataState = { mState -> mState.dataState }
  val extractControlPrec:
    (MultiPrec<LPrec, RPrec, DataPrec>) -> MultiPrec<LControlPrec, RControlPrec, UnitPrec> =
    { mPrec ->
      MultiPrec(
        analysis.leftSide.extractControlPrec.invoke(mPrec.leftPrec()),
        analysis.rightSide.extractControlPrec.invoke(mPrec.rightPrec()),
        UnitPrec.getInstance(),
      )
    }
  val side =
    MultiAnalysisSide(
      analysis,
      initFunc,
      combineStates,
      extractControlState,
      extractDataFromState,
      extractControlPrec,
    )
  return MultiBuilderResultPOJO(side, lts)
}
