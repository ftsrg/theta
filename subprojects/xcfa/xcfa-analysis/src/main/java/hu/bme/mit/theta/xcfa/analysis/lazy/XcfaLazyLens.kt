/*
 *  Copyright 2026 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.xcfa.analysis.lazy

import hu.bme.mit.theta.analysis.State
import hu.bme.mit.theta.analysis.algorithm.lazy.LazyState
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.prod2.Prod2State
import hu.bme.mit.theta.analysis.ptr.PtrState
import hu.bme.mit.theta.core.utils.Lens
import hu.bme.mit.theta.xcfa.analysis.XcfaState

private typealias LS<DConcr, DAbstr, CConcr, CAbstr> =
  LazyState<
    XcfaState<PtrState<Prod2State<out DConcr, out CConcr>>>,
    XcfaState<PtrState<Prod2State<out DAbstr, out CAbstr>>> >

fun <DConcr: State> createConcrDataLens() = object : Lens<LS<DConcr, *, *, *>, DConcr> {
  override fun get(
    state: LS<DConcr, *, *, *>
  ): DConcr {
    return state.concrState.sGlobal.innerState.state1
  }
  override fun set(
    state: LS<DConcr, *, *, *>,
    newConcrDataState: DConcr
  ): LS<DConcr, *, *, *> {
    val concrXcfaState = state.concrState
    val ptrState = concrXcfaState.sGlobal
    val prod2State = ptrState.innerState
    return state.withConcrState(
      concrXcfaState.withState(
        ptrState.copy(innerState = prod2State.with1(newConcrDataState))
      )
    )
  }
}

fun <CConcr: State> createConcrClockLens() = object : Lens<LS<*, *, CConcr, *>, CConcr> {
  override fun get(
    state: LS<*, *, CConcr, *>
  ): CConcr {
    return state.concrState.sGlobal.innerState.state2
  }
  override fun set(
    state: LS<*, *, CConcr, *>,
    newConcrClockState: CConcr
  ): LS<*, *, CConcr, *> {
    val concrXcfaState = state.concrState
    val ptrState = concrXcfaState.sGlobal
    val prod2State = ptrState.innerState
    return state.withConcrState(
      concrXcfaState.withState(
        ptrState.copy(innerState = prod2State.with2(newConcrClockState))
      )
    )
  }
}

fun <CAbstr: ExprState> createAbstrClockLens() = object : Lens<LS<*, *, *, CAbstr>, CAbstr> {
  override fun get(
    state: LS<*, *, *, CAbstr>
  ): CAbstr {
    return state.abstrState.sGlobal.innerState.state2
  }
  override fun set(
    state: LS<*, *, *, CAbstr>,
    newAbstrClockState: CAbstr
  ): LS<*, *, *, CAbstr> {
    val abstrXcfaState = state.abstrState
    val ptrState = abstrXcfaState.sGlobal
    val prod2State = ptrState.innerState
    return state.withAbstrState(
      abstrXcfaState.withState(
        ptrState.copy(innerState = prod2State.with2(newAbstrClockState))
      )
    )
  }
}

fun <CConcr: State, CAbstr: ExprState> createLazyClockLens() =
  object : Lens<LS<*, *, CConcr, CAbstr>, LazyState<CConcr, CAbstr>> {
    val concrLens = createConcrClockLens<CConcr>() as Lens<LS<*, *, CConcr, CAbstr>, CConcr>
    val abstrLens = createAbstrClockLens<CAbstr>() as Lens<LS<*, *, CConcr, CAbstr>, CAbstr>
    override fun get(
      state: LS<*, *, CConcr, CAbstr>
    ): LazyState<CConcr, CAbstr> {
      val concrState = concrLens.get(state)
      return if (concrState.isBottom)
        LazyState.bottom(concrState)
      else LazyState.of(concrState, abstrLens.get(state))
    }
    override fun set(
      state: LS<*, *, CConcr, CAbstr>,
      newLazyState: LazyState<CConcr, CAbstr>
    ): LS<*, *, CConcr, CAbstr> {
      val newConcrState = concrLens.set(state, newLazyState.concrState).concrState
      val newAbstrState = abstrLens.set(state, newLazyState.abstrState).abstrState
      return LazyState.of(newConcrState, newAbstrState)
    }
  }

fun <DConcr: State, CConcr: State> createConcrProd2Lens() =
  object : Lens<LS<DConcr, *, CConcr, *>, Prod2State<out DConcr, out CConcr>> {
    override fun get(
      state: LS<DConcr, *, CConcr, *>
    ): Prod2State<out DConcr, out CConcr> {
      return state.concrState.sGlobal.innerState
    }
    override fun set(
      state: LS<DConcr, *, CConcr, *>,
      newConcrState: Prod2State<out DConcr, out CConcr>
    ): LS<DConcr, *, CConcr, *> {
      throw UnsupportedOperationException()
    }
  }

fun createConcrLens() =
  object : Lens<LS<*, *, *, *>, XcfaState<PtrState<Prod2State<*, *>>>> {
    override fun get(
      state: LS<*, *, *, *>
    ): XcfaState<PtrState<Prod2State<*, *>>> {
      return state.concrState
    }
    override fun set(
      state: LS<*, *, *, *>,
      newConcrState: XcfaState<PtrState<Prod2State<*, *>>>
    ): LS<*, *, *, *> {
      return state.withConcrState(newConcrState)
    }
  }
