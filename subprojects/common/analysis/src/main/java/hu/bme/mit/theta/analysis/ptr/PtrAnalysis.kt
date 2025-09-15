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
package hu.bme.mit.theta.analysis.ptr

import hu.bme.mit.theta.analysis.*
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.StmtAction
import hu.bme.mit.theta.core.stmt.Stmt

/**
 * Pointer analysis in CEGAR
 *
 * PtrState has some inner state (presumably PredState or ExplState), and a list of tuples (per SMT
 * type) that store last-known values of specific memory places.
 *
 * PtrTransFunc takes a list of statements, possibly including Dereferences in both left- and
 * right-hand sides in them, and using the last-known values (with havoc as fallback) constructs
 * safeguards that constraint how the expression may read from writes. New values are placed in the
 * resulting state. Values are never erased.
 *
 * PtrAction is a special StmtAction, which needs some pre-processing based on the current known
 * memory values.
 */
class PtrAnalysis<S : ExprState, P : Prec>(
  private val innerAnalysis: Analysis<S, ExprAction, P>,
  private val isHavoc: Boolean = false,
) : Analysis<PtrState<S>, PtrAction, PtrPrec<P>> {

  override fun getPartialOrd(): PartialOrd<PtrState<S>> =
    innerAnalysis.partialOrd.getPtrPartialOrd()

  override fun getInitFunc(): InitFunc<PtrState<S>, PtrPrec<P>> =
    innerAnalysis.initFunc.getPtrInitFunc()

  override fun getTransFunc(): TransFunc<PtrState<S>, PtrAction, PtrPrec<P>> =
    innerAnalysis.transFunc.getPtrTransFunc(isHavoc)
}

fun <S : ExprState> PartialOrd<S>.getPtrPartialOrd(): PartialOrd<PtrState<S>> =
  PartialOrd { state1, state2 ->
    isLeq(state1.innerState, state2.innerState)
  }

fun <S : ExprState, P : Prec> InitFunc<S, P>.getPtrInitFunc(): InitFunc<PtrState<S>, PtrPrec<P>> =
  InitFunc { prec ->
    getInitStates(prec.innerPrec.patch(emptyMap())).map { PtrState(it) }
  }

fun <S : ExprState, P : Prec> TransFunc<S, in ExprAction, P>.getPtrTransFunc(
  isHavoc: Boolean = false
): TransFunc<PtrState<S>, PtrAction, PtrPrec<P>> = TransFunc { state, action, prec ->
  val writeTriples = action.nextWriteTriples()
  val patchedPrec = prec.innerPrec.patch(writeTriples)
  val exprAction: ExprAction =
    if (isHavoc) {
      object : StmtAction() {
        override fun getStmts(): List<Stmt> =
          action.havocStmts() // stmts without pre- and postconditions
      }
    } else {
      action
    }
  getSuccStates(state.innerState, exprAction, patchedPrec).map {
    PtrState(it.repatch(), action.cnts.values.maxOrNull() ?: action.inCnt)
  }
}
