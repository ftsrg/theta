/*
 * Copyright 2024 Budapest University of Technology and Economics
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *     http://www.apache.org/licenses/LICENSE-2.0
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package hu.bme.mit.theta.analysis.multi

import hu.bme.mit.theta.analysis.Analysis
import hu.bme.mit.theta.analysis.InitFunc
import hu.bme.mit.theta.analysis.LTS
import hu.bme.mit.theta.analysis.PartialOrd
import hu.bme.mit.theta.analysis.TransFunc
import hu.bme.mit.theta.analysis.expr.ExprState
import hu.bme.mit.theta.analysis.expr.StmtAction
import hu.bme.mit.theta.analysis.multi.builder.stmt.StmtMultiBuilder
import hu.bme.mit.theta.analysis.multi.stmt.ExprMultiState
import hu.bme.mit.theta.analysis.unit.UnitPrec
import hu.bme.mit.theta.analysis.unit.UnitState
import hu.bme.mit.theta.core.stmt.SkipStmt
import hu.bme.mit.theta.core.stmt.Stmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolType
import org.junit.jupiter.api.Test


class MultiAnalysisTest {

    val multiUnitPrec = MultiPrec(UnitPrec.getInstance(), UnitPrec.getInstance(), UnitPrec.getInstance())

    class NumberedState(val num: Int) : ExprState {

        override fun toExpr(): Expr<BoolType?>? = True()

        override fun isBottom(): Boolean = false

    }

    class NumberedAction() : StmtAction() {

        override fun getStmts(): List<Stmt?>? {
            return listOf(SkipStmt.getInstance())
        }

    }

    class NumberedAnalysis : Analysis<NumberedState, NumberedAction, UnitPrec> {

        override fun getPartialOrd(): PartialOrd<NumberedState>? =
            object : PartialOrd<NumberedState> {
                override fun isLeq(
                    state1: NumberedState?,
                    state2: NumberedState?
                ): Boolean = state1!!.num <= state2!!.num

            }

        override fun getInitFunc(): InitFunc<NumberedState?, UnitPrec?>? =
            object : InitFunc<NumberedState?, UnitPrec?> {
                override fun getInitStates(
                    prec: UnitPrec?
                ): Collection<NumberedState?>? = listOf<NumberedState>(NumberedState(0))

            }

        override fun getTransFunc(): TransFunc<NumberedState?, NumberedAction?, UnitPrec?>? =
            object : TransFunc<NumberedState?, NumberedAction?, UnitPrec?> {
                override fun getSuccStates(
                    state: NumberedState?,
                    action: NumberedAction?,
                    prec: UnitPrec?
                ): Collection<NumberedState?>? = listOf(NumberedState(state!!.num + 1))

            }

    }

    class NumberedLTS : LTS<NumberedState, NumberedAction> {

        override fun getEnabledActionsFor(
            state: NumberedState?
        ): Collection<NumberedAction?>? = listOf(NumberedAction())

    }

    @Test
    fun test() {

        val side: MultiAnalysisSide<NumberedState, UnitState, NumberedState, NumberedAction, UnitPrec, UnitPrec> =
            MultiAnalysisSide(
                NumberedAnalysis(),
                object : InitFunc<NumberedState, UnitPrec> {
                    override fun getInitStates(
                        prec: UnitPrec?
                    ): Collection<NumberedState?>? = listOf(NumberedState(0))
                },
                { c: NumberedState, _: UnitState -> c },
                { c: NumberedState -> c },
                { c: NumberedState -> UnitState.getInstance() },
                { p: UnitPrec -> p }
            )

        val builderResult = StmtMultiBuilder(side, NumberedLTS())
            .addRightSide(side, NumberedLTS())
            .build<UnitPrec>(
                { ms: ExprMultiState<NumberedState, NumberedState, UnitState> -> if (ms.sourceSide == MultiSide.RIGHT || ms.leftState.num % 2 == 1) MultiSide.LEFT else MultiSide.RIGHT },
                object : InitFunc<UnitState, UnitPrec> {
                    override fun getInitStates(
                        prec: UnitPrec?
                    ): Collection<UnitState?>? = listOf(UnitState.getInstance())
                }
            )

        val multiAnalysis = builderResult.side.analysis
        val initStates = multiAnalysis.initFunc.getInitStates(multiUnitPrec)
        val initState = initStates.single()

        assert(initStates.size == 1)
        assert(initState.leftState.num == 0 && initState.rightState.num == 0)

        var action = builderResult.lts.getEnabledActionsFor(initState).single()

        val succ1State = multiAnalysis.transFunc.getSuccStates(initState, action, multiUnitPrec).single()
        assert(succ1State.leftState.num == 0 && succ1State.rightState.num == 1)
        action = builderResult.lts.getEnabledActionsFor(succ1State).single()

        val succ2State = multiAnalysis.transFunc.getSuccStates(succ1State, action, multiUnitPrec).single()
        assert(succ2State.leftState.num == 1 && succ2State.rightState.num == 1)
        action = builderResult.lts.getEnabledActionsFor(succ2State).single()

        val succ3State = multiAnalysis.transFunc.getSuccStates(succ2State, action, multiUnitPrec).single()
        assert(succ3State.leftState.num == 2 && succ3State.rightState.num == 1)

        assert(multiAnalysis.partialOrd.isLeq(succ2State, succ3State))

    }


}