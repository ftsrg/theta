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
package hu.bme.mit.theta.cfa.analysis

import hu.bme.mit.theta.analysis.Prec
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.unit.UnitPrec
import hu.bme.mit.theta.analysis.unit.UnitState
import hu.bme.mit.theta.cfa.analysis.prec.GlobalCfaPrec

fun <S : ExprState> cfaCombineStates(cfaState: CfaState<UnitState>, dataState: S): CfaState<S> {
  return CfaState.of(cfaState.loc, dataState)
}

fun cfaExtractControlState(cfaState: CfaState<*>): CfaState<UnitState> {
  return CfaState.of(cfaState.loc, UnitState.getInstance())
}

fun <S : ExprState> cfaExtractDataState(cfaState: CfaState<S>): S {
  return cfaState.state
}

fun cfaExtractControlPrec(p: CfaPrec<out Prec>): CfaPrec<UnitPrec> {
  return GlobalCfaPrec.create(UnitPrec.getInstance())
}
