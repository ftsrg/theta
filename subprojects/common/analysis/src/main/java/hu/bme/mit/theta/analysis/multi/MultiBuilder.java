/*
 *  Copyright 2024 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.analysis.multi;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;

import java.util.function.BiFunction;
import java.util.function.Function;

public final class MultiBuilder {

    public static <LState extends State, LBlank extends State, LAction extends Action, DataState extends State, LPrec extends Prec, LBlankPrec extends Prec>
    LeftSideAdded<LState, DataState, LBlank, LAction, LPrec, LBlankPrec> initWithLeftSide(
            Analysis<LState, ? super LAction, ? super LPrec> analysis, LTS<? super LState, LAction> lts, BiFunction<LBlank, DataState, LState> combineStates, Function<LState, LBlank> stripDataFromState, Function<LState, DataState> extractDataFromState, InitFunc<LBlank, LBlankPrec> initFunc, Function<LPrec, LBlankPrec> stripDataFromPrec
    ) {
        return new LeftSideAdded<>(analysis, combineStates, stripDataFromState, extractDataFromState, lts, initFunc, stripDataFromPrec);
    }

    public record Result<LState extends State, RState extends State, DataState extends State, LBlank extends State, RBlank extends State,
            LAction extends Action, RAction extends Action,
            LPrec extends Prec, RPrec extends Prec, DataPrec extends Prec, LBlankPrec extends Prec, RBlankPrec extends Prec,
            MState extends MultiState<LBlank, RBlank, DataState>, MAction extends MultiAction<LAction, RAction>>
            (MultiAnalysis<LState, RState, DataState, LBlank, RBlank, LAction, RAction, LPrec, RPrec, DataPrec, LBlankPrec, RBlankPrec, MState, MAction> analysis,
             MultiLts<LState, RState, DataState, LBlank, RBlank, LAction, RAction, MState, MAction> lts) {
    }

    public static class LeftSideAdded<LState extends State, DataState extends State, LBlank extends State, LAction extends Action, LPrec extends Prec, LBlankPrec extends Prec> {
        private final MultiAnalysis.Side<LState, DataState, LBlank, LAction, LPrec, LBlankPrec> side;
        private final LTS<? super LState, LAction> lts;

        LeftSideAdded(Analysis<LState, ? super LAction, ? super LPrec> analysis, BiFunction<LBlank, DataState, LState> combineStates, Function<LState, LBlank> stripDataFromState,
                      Function<LState, DataState> extractDataFromState, LTS<? super LState, LAction> lts, InitFunc<LBlank, LBlankPrec> initFunc, Function<LPrec, LBlankPrec> stripDataFromPrec) {
            this.lts = lts;
            this.side = new MultiAnalysis.Side<>(analysis, initFunc, combineStates, stripDataFromState, extractDataFromState, stripDataFromPrec);
        }

        public <RState extends State, RBlank extends State, RAction extends Action, RPrec extends Prec, RBlankPrec extends Prec>
        BothSidesDone<LState, RState, DataState, LBlank, RBlank, LAction, RAction, LPrec, RPrec, LBlankPrec, RBlankPrec>
        addRightSide(Analysis<RState, ? super RAction, ? super RPrec> analysis, LTS<RState, RAction> rightLts,
                     BiFunction<RBlank, DataState, RState> combineStates, Function<RState, RBlank> stripDataFromState, Function<RState, DataState> extractDataFromState,
                     InitFunc<RBlank, RBlankPrec> initFunc, Function<RPrec, RBlankPrec> stripDataFromPrec) {
            MultiAnalysis.Side<RState, DataState, RBlank, RAction, RPrec, RBlankPrec> rightSide = new MultiAnalysis.Side<>(analysis, initFunc, combineStates, stripDataFromState, extractDataFromState, stripDataFromPrec);
            return new BothSidesDone<>(side, lts, rightSide, rightLts);
        }

    }

    public static class BothSidesDone<LState extends State, RState extends State, DataState extends State, LBlank extends State, RBlank extends State,
            LAction extends Action, RAction extends Action,
            LPrec extends Prec, RPrec extends Prec, LBlankPrec extends Prec, RBlankPrec extends Prec> {
        private final MultiAnalysis.Side<LState, DataState, LBlank, LAction, LPrec, LBlankPrec> leftSide;
        private final LTS<? super LState, LAction> leftLts;
        private final MultiAnalysis.Side<RState, DataState, RBlank, RAction, RPrec, RBlankPrec> rightSide;
        private final LTS<? super RState, RAction> rightLts;

        BothSidesDone(MultiAnalysis.Side<LState, DataState, LBlank, LAction, LPrec, LBlankPrec> leftSide, LTS<? super LState, LAction> leftLts, MultiAnalysis.Side<RState, DataState, RBlank, RAction, RPrec, RBlankPrec> rightSide, LTS<? super RState, RAction> rightLts) {
            this.leftSide = leftSide;
            this.leftLts = leftLts;
            this.rightSide = rightSide;
            this.rightLts = rightLts;
        }

        public <DataPrec extends Prec, MState extends MultiState<LBlank, RBlank, DataState>, MAction extends MultiAction<LAction, RAction>>
        Result<LState, RState, DataState, LBlank, RBlank, LAction, RAction, LPrec, RPrec, DataPrec, LBlankPrec, RBlankPrec, MState, MAction>
        build(Function<MState, MultiSourceSide> defineNextSide, InitFunc<DataState, DataPrec> dataInitFunc,
              MultiAnalysisBuilderFunc<LState, RState, DataState, LBlank, RBlank, LAction, RAction, LPrec, RPrec, DataPrec, LBlankPrec, RBlankPrec, MState, MAction,
                      MultiAnalysis<LState, RState, DataState, LBlank, RBlank, LAction, RAction, LPrec, RPrec, DataPrec, LBlankPrec, RBlankPrec, MState, MAction>> analysisBuilderFunc,
              MultiLtsBuilderFunc<LState, RState, DataState, LBlank, RBlank, LAction, RAction, MState, MAction, MultiLts<LState, RState, DataState, LBlank, RBlank, LAction, RAction, MState, MAction>> ltsBuilderFunc) {
            return new Result<>(
                    analysisBuilderFunc.build(leftSide, rightSide, defineNextSide, dataInitFunc),
                    ltsBuilderFunc.build(leftLts, leftSide.combineStates(), rightLts, rightSide.combineStates(), defineNextSide)
            );
        }

    }

}
