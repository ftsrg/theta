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
package hu.bme.mit.theta.analysis.multi.builder.stmt;

import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.StmtAction;
import hu.bme.mit.theta.analysis.multi.MultiAnalysisSide;
import hu.bme.mit.theta.analysis.multi.NextSideFunctions;
import hu.bme.mit.theta.analysis.multi.builder.MultiBuilderResultKt;
import hu.bme.mit.theta.analysis.multi.builder.MultiBuilderResultPOJO;
import hu.bme.mit.theta.analysis.multi.stmt.ExprMultiState;
import hu.bme.mit.theta.analysis.multi.stmt.StmtMultiAction;
import hu.bme.mit.theta.analysis.multi.stmt.StmtMultiAnalysis;
import hu.bme.mit.theta.analysis.multi.stmt.StmtMultiLts;
import hu.bme.mit.theta.analysis.unit.UnitState;

@SuppressWarnings("java:S119")
public final class StmtMultiBuilderPair<
        LState extends ExprState,
        LBlank extends ExprState,
        LAction extends StmtAction,
        DataState extends ExprState,
        LPrec extends Prec,
        LBlankPrec extends Prec,
        RState extends ExprState,
        RBlank extends ExprState,
        RAction extends StmtAction,
        RPrec extends Prec,
        RBlankPrec extends Prec> {

    private final MultiAnalysisSide<LState, DataState, LBlank, LAction, LPrec, LBlankPrec> leftSide;
    private final LTS<? super LState, LAction> leftLts;
    private final MultiAnalysisSide<RState, DataState, RBlank, RAction, RPrec, RBlankPrec>
            rightSide;
    private final LTS<? super RState, RAction> rightLts;

    StmtMultiBuilderPair(
            MultiAnalysisSide<LState, DataState, LBlank, LAction, LPrec, LBlankPrec> leftSide,
            LTS<? super LState, LAction> leftLts,
            MultiAnalysisSide<RState, DataState, RBlank, RAction, RPrec, RBlankPrec> rightSide,
            LTS<? super RState, RAction> rightLts) {
        this.leftSide = leftSide;
        this.leftLts = leftLts;
        this.rightSide = rightSide;
        this.rightLts = rightLts;
    }

    public <DataPrec extends Prec>
            MultiBuilderResultPOJO<
                            LState,
                            RState,
                            DataState,
                            LBlank,
                            RBlank,
                            LAction,
                            RAction,
                            LPrec,
                            RPrec,
                            DataPrec,
                            LBlankPrec,
                            RBlankPrec,
                            ExprMultiState<LBlank, RBlank, DataState>,
                            ExprMultiState<LBlank, RBlank, UnitState>,
                            StmtMultiAction<LAction, RAction>,
                            StmtMultiLts<
                                    LState, RState, DataState, LBlank, RBlank, LAction, RAction>>
                    build(
                            NextSideFunctions.NextSideFunction<
                                            LBlank,
                                            RBlank,
                                            DataState,
                                            ExprMultiState<LBlank, RBlank, DataState>>
                                    nextSideFunction,
                            InitFunc<DataState, DataPrec> dataInitFunc) {
        return MultiBuilderResultKt.multiBuilderResult(
                StmtMultiAnalysis.of(
                        leftSide, rightSide, nextSideFunction::defineNextSide, dataInitFunc),
                StmtMultiLts.of(
                        leftLts,
                        (lbs, ds) -> leftSide.getCombineStates().invoke(lbs, ds),
                        rightLts,
                        (rbs, ds) -> rightSide.getCombineStates().invoke(rbs, ds),
                        nextSideFunction::defineNextSide));
    }
}
