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

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.analysis.State;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.stream.Stream;

@SuppressWarnings("java:S119")
public abstract class MultiLts<
                LState extends State,
                RState extends State,
                DataState extends State,
                LBlank extends State,
                RBlank extends State,
                LAction extends Action,
                RAction extends Action,
                MState extends MultiState<LBlank, RBlank, DataState>,
                MAction extends MultiAction<LAction, RAction>>
        implements LTS<MState, MAction> {

    private final Function<MState, MultiSide> defineNextSide;
    private final Side<LState, DataState, LBlank, LAction> left;
    private final Side<RState, DataState, RBlank, RAction> right;

    protected MultiLts(
            Function<MState, MultiSide> defineNextSide,
            Side<LState, DataState, LBlank, LAction> left,
            Side<RState, DataState, RBlank, RAction> right) {
        this.defineNextSide = defineNextSide;
        this.left = left;
        this.right = right;
    }

    protected static <S extends State, Data extends State, Blank extends State, A extends Action>
            Side<S, Data, Blank, A> createSide(
                    LTS<? super S, A> lts, BiFunction<Blank, Data, S> combineStates) {
        return new Side<>(lts, combineStates);
    }

    protected abstract MAction wrapLeftAction(LAction action);

    protected abstract MAction wrapRightAction(RAction action);

    @Override
    @SuppressWarnings("java:S2203")
    public Collection<MAction> getEnabledActionsFor(MState state) {
        MultiSide nextSide = defineNextSide.apply(state);
        List<MAction> enabledActions = new LinkedList<>();
        if (nextSide != MultiSide.RIGHT) {
            Stream<LAction> actionStream =
                    left
                            .lts
                            .getEnabledActionsFor(
                                    left.combineStates.apply(
                                            state.getLeftState(), state.getDataState()))
                            .stream();
            Stream<MAction> multiActionStream = actionStream.map(this::wrapLeftAction);
            multiActionStream.forEach(enabledActions::add);
        }
        if (nextSide != MultiSide.LEFT) {
            Stream<RAction> actionStream =
                    right
                            .lts
                            .getEnabledActionsFor(
                                    right.combineStates.apply(
                                            state.getRightState(), state.getDataState()))
                            .stream();
            Stream<MAction> multiActionStream = actionStream.map(this::wrapRightAction);
            multiActionStream.forEach(enabledActions::add);
        }
        return enabledActions;
    }

    public Function<MState, MultiSide> getDefineNextSide() {
        return defineNextSide;
    }

    protected record Side<
            S extends State, Data extends State, Blank extends State, A extends Action>(
            LTS<? super S, A> lts, BiFunction<Blank, Data, S> combineStates) {}
}
