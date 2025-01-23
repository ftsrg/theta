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
package hu.bme.mit.theta.analysis.multi;

import hu.bme.mit.theta.analysis.*;
import hu.bme.mit.theta.analysis.unit.UnitState;
import java.util.function.Function;

/**
 * @param <LState> Type of combined (with data) state of left formalism
 * @param <RState> Type of combined (with data) state of right formalism
 * @param <DataState> Type of data state
 * @param <LControl> Type of control state from left formalism
 * @param <RControl> Type of control state from right formalism
 * @param <LAction> Type of action from left formalism
 * @param <RAction> Type of action from right formalism
 * @param <LPrec> Type of precision of left formalism
 * @param <RPrec> Type of precision of right formalism
 * @param <DataPrec> Type of data precision (formalism independent)
 */
@SuppressWarnings("java:S119")
public abstract class MultiAnalysis<
                LState extends State,
                RState extends State,
                DataState extends State,
                LControl extends State,
                RControl extends State,
                LAction extends Action,
                RAction extends Action,
                LPrec extends Prec,
                RPrec extends Prec,
                DataPrec extends Prec,
                LControlPrec extends Prec,
                RControlPrec extends Prec,
                MState extends MultiState<LControl, RControl, DataState>,
                MBlankState extends MultiState<LControl, RControl, UnitState>,
                MAction extends MultiAction<LAction, RAction>>
        implements Analysis<MState, MAction, MultiPrec<LPrec, RPrec, DataPrec>> {

    protected final MultiAnalysisSide<LState, DataState, LControl, LAction, LPrec, LControlPrec>
            leftSide;
    protected final MultiAnalysisSide<RState, DataState, RControl, RAction, RPrec, RControlPrec>
            rightSide;
    private final PartialOrd<MState> partialOrder;
    private final InitFunc<MState, MultiPrec<LPrec, RPrec, DataPrec>> initFunc;
    private final TransFunc<MState, MAction, MultiPrec<LPrec, RPrec, DataPrec>> transFunc;

    protected MultiAnalysis(
            Function<MState, MultiSide> defineNextSide,
            MultiAnalysisSide<LState, DataState, LControl, LAction, LPrec, LControlPrec> leftSide,
            MultiAnalysisSide<RState, DataState, RControl, RAction, RPrec, RControlPrec> rightSide,
            InitFunc<DataState, DataPrec> dataInitFunc) {
        this.leftSide = leftSide;
        this.rightSide = rightSide;
        this.partialOrder =
                new MultiPartialOrd<>(
                        leftSide.getAnalysis().getPartialOrd(),
                        leftSide.getCombineStates(),
                        rightSide.getAnalysis().getPartialOrd(),
                        rightSide.getCombineStates());
        this.initFunc =
                new MultiInitFunc<>(
                        this::createInitialState,
                        dataInitFunc,
                        leftSide.getExtractControlPrec(),
                        leftSide.getControlInitFunc(),
                        rightSide.getExtractControlPrec(),
                        rightSide.getControlInitFunc());
        this.transFunc =
                new MultiTransFunc<>(
                        defineNextSide::apply,
                        this::createState,
                        leftSide.getAnalysis().getTransFunc(),
                        leftSide.getCombineStates(),
                        leftSide.getExtractControlState(),
                        leftSide.getExtractDataState(),
                        rightSide.getAnalysis().getTransFunc(),
                        rightSide.getCombineStates(),
                        rightSide.getExtractControlState(),
                        rightSide.getExtractDataState());
    }

    public MultiAnalysisSide<LState, DataState, LControl, LAction, LPrec, LControlPrec>
            getLeftSide() {
        return leftSide;
    }

    public MultiAnalysisSide<RState, DataState, RControl, RAction, RPrec, RControlPrec>
            getRightSide() {
        return rightSide;
    }

    protected abstract MState createInitialState(
            LControl leftState, RControl rightState, DataState dataState);

    public abstract MState createState(
            LControl leftState, RControl rightState, DataState dataState, MultiSide sourceSide);

    public abstract MBlankState createControlState(
            LControl leftState, RControl rightState, MultiSide sourceSide);

    public MBlankState createControlInitState(LControl leftState, RControl rightState) {
        return createControlState(leftState, rightState, null);
    }

    @Override
    public PartialOrd<MState> getPartialOrd() {
        return partialOrder;
    }

    @Override
    public InitFunc<MState, MultiPrec<LPrec, RPrec, DataPrec>> getInitFunc() {
        return initFunc;
    }

    @Override
    public TransFunc<MState, MAction, MultiPrec<LPrec, RPrec, DataPrec>> getTransFunc() {
        return transFunc;
    }
}
