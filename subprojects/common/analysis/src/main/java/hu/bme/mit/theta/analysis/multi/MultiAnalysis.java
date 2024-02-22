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
import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.TransFunc;

import java.util.Collection;
import java.util.HashSet;
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * @param <LState>    Type of combined (with data) state of left formalism
 * @param <RState>    Type of combined (with data) state of right formalism
 * @param <DataState> Type of data state
 * @param <LBlank>    Type of blank state from left formalism
 * @param <RBlank>    Type of blank state from right formalism
 * @param <LAction>   Type of action from left formalism
 * @param <RAction>   Type of action from right formalism
 * @param <LPrec>     Type of precision of left formalism
 * @param <RPrec>     Type of precision of right formalism
 * @param <DataPrec>  Type of data precision (formalism independent)
 */
public abstract class MultiAnalysis<LState extends State, RState extends State, DataState extends State, LBlank extends State, RBlank extends State,
        LAction extends Action, RAction extends Action,
        LPrec extends Prec, RPrec extends Prec, DataPrec extends Prec, LBlankPrec extends Prec, RBlankPrec extends Prec,
        MState extends MultiState<LBlank, RBlank, DataState>, MAction extends MultiAction<LAction, RAction>>
        implements Analysis<MState, MAction, MultiPrec<LPrec, RPrec, DataPrec>> {

    private final Function<MState, MultiSourceSide> defineNextSide;

    private final Side<LState, DataState, LBlank, LAction, LPrec, LBlankPrec> leftSide;
    private final Side<RState, DataState, RBlank, RAction, RPrec, RBlankPrec> rightSide;

    private final InitFunc<DataState, DataPrec> dataInitFunc;

    protected MultiAnalysis(Function<MState, MultiSourceSide> defineNextSide, Side<LState, DataState, LBlank, LAction, LPrec, LBlankPrec> leftSide, Side<RState, DataState, RBlank, RAction, RPrec, RBlankPrec> rightSide, InitFunc<DataState, DataPrec> dataInitFunc) {
        this.defineNextSide = defineNextSide;
        this.leftSide = leftSide;
        this.rightSide = rightSide;
        this.dataInitFunc = dataInitFunc;
    }

    abstract MState createInitialState(LBlank leftState, RBlank rightState, DataState dataState);

    abstract MState createState(LBlank leftState, RBlank rightState, DataState dataState, MultiSourceSide sourceSide);

    @Override
    public PartialOrd<MState> getPartialOrd() {
        return ((state1, state2) -> leftSide.analysis.getPartialOrd().isLeq(leftSide.combineStates.apply(state1.getLeftState(), state1.getDataState()), leftSide.combineStates.apply(state2.getLeftState(), state2.getDataState()))
                && rightSide.analysis.getPartialOrd().isLeq(rightSide.combineStates.apply(state1.getRightState(), state1.getDataState()), rightSide.combineStates.apply(state2.getRightState(), state2.getDataState()))
                && ((!state1.getSourceMattersInEquality() && !state2.getSourceMattersInEquality()) || (state1.getSourceSide() == state2.getSourceSide())));
    }

    @Override
    public InitFunc<MState, MultiPrec<LPrec, RPrec, DataPrec>> getInitFunc() {
        return (prec -> {
            LBlankPrec leftInitPrec = leftSide.stripDataFromPrec.apply(prec.leftPrec());
            RBlankPrec rightInitPrec = rightSide.stripDataFromPrec.apply(prec.rightPrec());
            Collection<LBlank> leftInitStates = new HashSet<>(leftSide.initFunc.getInitStates(leftInitPrec));
            Collection<RBlank> rightInitStates = new HashSet<>(rightSide.initFunc.getInitStates(rightInitPrec));
            Collection<? extends DataState> dataInitStates = dataInitFunc.getInitStates(prec.dataPrec());
            Collection<MState> resultSet = new HashSet<>();
            for (LBlank leftInitState :
                    leftInitStates) {
                for (RBlank rightInitState :
                        rightInitStates) {
                    for (DataState dataInitState :
                            dataInitStates) {
                        resultSet.add(createInitialState(leftInitState, rightInitState, dataInitState));
                    }
                }
            }
            return resultSet;
        });
    }

    @Override
    public TransFunc<MState, MAction, MultiPrec<LPrec, RPrec, DataPrec>> getTransFunc() {
        return ((state, action, prec) -> switch (defineNextSide.apply(state)) {
            case LEFT -> {
                final var succStates = leftSide.analysis.getTransFunc().getSuccStates(leftSide.combineStates().apply(state.getLeftState(), state.getDataState()), action.getLeftAction(), prec.leftPrec());
                final Stream<MState> multiStateStream = succStates.stream().map(s -> createState(leftSide.stripDataFromState().apply(s), state.getRightState(), leftSide.extractDataFromState.apply(s), MultiSourceSide.LEFT));
                yield multiStateStream.collect(Collectors.toSet());
            }
            case RIGHT -> {
                final var succStates = rightSide.analysis.getTransFunc().getSuccStates(rightSide.combineStates.apply(state.getRightState(), state.getDataState()), action.getRightAction(), prec.rightPrec());
                final Stream<MState> multiStateStream = succStates.stream().map(s -> createState(state.getLeftState(), rightSide.stripDataFromState.apply(s), rightSide.extractDataFromState.apply(s), MultiSourceSide.RIGHT));
                yield multiStateStream.collect(Collectors.toSet());
            }
        });
    }

    public record Side<S extends State, DataS extends State, BlankS extends State, A extends Action, P extends Prec, BlankP extends Prec>
            (Analysis<S, ? super A, ? super P> analysis, InitFunc<BlankS, BlankP> initFunc,
             BiFunction<BlankS, DataS, S> combineStates, Function<S, BlankS> stripDataFromState,
             Function<S, DataS> extractDataFromState, Function<P, BlankP> stripDataFromPrec) {
    }
}
