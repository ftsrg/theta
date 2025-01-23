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
package hu.bme.mit.theta.xsts.analysis.util

import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.unit.UnitPrec
import hu.bme.mit.theta.analysis.unit.UnitState
import hu.bme.mit.theta.xsts.analysis.XstsState

fun <S : ExprState> xstsCombineStates(xstsState: XstsState<UnitState>, dataState: S): XstsState<S> {
  return XstsState.of(dataState, xstsState.lastActionWasEnv(), xstsState.isInitialized)
}

fun xstsExtractControlState(xstsState: XstsState<*>): XstsState<UnitState> {
  return XstsState.of(
    UnitState.getInstance(),
    xstsState.lastActionWasEnv(),
    xstsState.isInitialized,
  )
}

fun <S : ExprState> xstsExtractDataState(xstsState: XstsState<S>): S {
  return xstsState.state
}

fun <P : Prec> xstsExtractControlPrec(p: P): UnitPrec = UnitPrec.getInstance()
