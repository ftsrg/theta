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
package hu.bme.mit.theta.analysis.multi.stmt;

import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.StmtAction;
import hu.bme.mit.theta.analysis.multi.MultiAnalysis;
import hu.bme.mit.theta.analysis.multi.MultiAnalysisSide;
import hu.bme.mit.theta.analysis.multi.MultiSide;
import hu.bme.mit.theta.analysis.unit.UnitState;
import java.util.function.Function;

@SuppressWarnings("java:S119")
public final class StmtMultiAnalysis<
                LState extends ExprState,
                RState extends ExprState,
                DataState extends ExprState,
                LBlank extends ExprState,
                RBlank extends ExprState,
                LAction extends StmtAction,
                RAction extends StmtAction,
                LPrec extends Prec,
                RPrec extends Prec,
                DataPrec extends Prec,
                LBlankPrec extends Prec,
                RBlankPrec extends Prec>
        extends MultiAnalysis<
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
                StmtMultiAction<LAction, RAction>> {

    private StmtMultiAnalysis(
            Function<ExprMultiState<LBlank, RBlank, DataState>, MultiSide> defineNextSide,
            MultiAnalysisSide<LState, DataState, LBlank, LAction, LPrec, LBlankPrec> leftSide,
            MultiAnalysisSide<RState, DataState, RBlank, RAction, RPrec, RBlankPrec> rightSide,
            InitFunc<DataState, DataPrec> dataInitFunc) {
        super(defineNextSide, leftSide, rightSide, dataInitFunc);
    }

    public static <
                    LState extends ExprState,
                    RState extends ExprState,
                    DataState extends ExprState,
                    LBlank extends ExprState,
                    RBlank extends ExprState,
                    LAction extends StmtAction,
                    RAction extends StmtAction,
                    LPrec extends Prec,
                    RPrec extends Prec,
                    DataPrec extends Prec,
                    LBlankPrec extends Prec,
                    RBlankPrec extends Prec>
            StmtMultiAnalysis<
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
                            RBlankPrec>
                    of(
                            MultiAnalysisSide<LState, DataState, LBlank, LAction, LPrec, LBlankPrec>
                                    leftSide,
                            MultiAnalysisSide<RState, DataState, RBlank, RAction, RPrec, RBlankPrec>
                                    rightSide,
                            Function<ExprMultiState<LBlank, RBlank, DataState>, MultiSide>
                                    defineNextSide,
                            InitFunc<DataState, DataPrec> dataInitFunc) {
        return new StmtMultiAnalysis<>(defineNextSide, leftSide, rightSide, dataInitFunc);
    }

    @Override
    public ExprMultiState<LBlank, RBlank, DataState> createInitialState(
            LBlank leftState, RBlank rightState, DataState dataState) {
        return ExprMultiState.createInitial(leftState, rightState, dataState);
    }

    @Override
    public ExprMultiState<LBlank, RBlank, DataState> createState(
            LBlank leftState, RBlank rightState, DataState dataState, MultiSide sourceSide) {
        return ExprMultiState.create(leftState, rightState, dataState, sourceSide, true);
    }

    @Override
    public ExprMultiState<LBlank, RBlank, UnitState> createControlState(
            LBlank leftState, RBlank rightState, MultiSide sourceSide) {
        return ExprMultiState.create(
                leftState, rightState, UnitState.getInstance(), sourceSide, true);
    }
}
