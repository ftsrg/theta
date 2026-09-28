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
package hu.bme.mit.theta.analysis.algorithm.arg;

import static org.junit.jupiter.api.Assertions.assertEquals;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.stubs.ActionStub;
import hu.bme.mit.theta.analysis.stubs.PartialOrdStub;
import hu.bme.mit.theta.analysis.stubs.PrecStub;
import hu.bme.mit.theta.analysis.stubs.StateStub;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.junit.jupiter.api.Test;

public class ArgBuilderTest {

    private final State s0 = new StateStub("0");
    private final State s1 = new StateStub("1");
    private final State s2 = new StateStub("2");
    private final State s3 = new StateStub("3");
    private final Action a = new ActionStub("A");
    private final Action b = new ActionStub("B");
    private final Map<Action, List<State>> succStates = Map.of(a, List.of(s1, s2), b, List.of(s3));

    private final List<Collection<Action>> exploredActionsLog = new ArrayList<>();

    /** Fires only actions not explored yet from the state, like AASPOR does. */
    private final LTS<State, Action> lts =
            new LTS<>() {
                @Override
                public Collection<Action> getEnabledActionsFor(final State state) {
                    return state.equals(s0) ? succStates.keySet() : List.of();
                }

                @Override
                public <P extends Prec> Collection<Action> getEnabledActionsFor(
                        final State state, final Collection<Action> exploredActions, final P prec) {
                    exploredActionsLog.add(Set.copyOf(exploredActions));
                    final Collection<Action> actions = new ArrayList<>(getEnabledActionsFor(state));
                    actions.removeAll(exploredActions);
                    return actions;
                }
            };

    private final Analysis<State, Action, Prec> analysis =
            new Analysis<>() {
                @Override
                public PartialOrd<State> getPartialOrd() {
                    return new PartialOrdStub();
                }

                @Override
                public InitFunc<State, Prec> getInitFunc() {
                    return prec -> List.of(s0);
                }

                @Override
                public TransFunc<State, Action, Prec> getTransFunc() {
                    return (state, action, prec) ->
                            state.equals(s0) ? succStates.get(action) : List.of();
                }
            };

    /** An action with a successor pruned must be re-fired, even if another successor survived. */
    @Test
    public void testReExpandActionWithPrunedSuccessor() {
        final ArgBuilder<State, Action, Prec> builder =
                ArgBuilder.create(lts, analysis, s -> false);
        final Prec prec = new PrecStub();
        final ARG<State, Action> arg = builder.createArg();
        final ArgNode<State, Action> root = builder.init(arg, prec).iterator().next();
        assertEquals(3, builder.expand(root, prec).size());

        arg.prune(root.getSuccNodes().filter(n -> n.getState().equals(s2)).findAny().get());
        final Collection<ArgNode<State, Action>> restored = builder.expand(root, prec);
        assertEquals(Set.of(b), exploredActionsLog.get(1));
        assertEquals(List.of(s2), restored.stream().map(ArgNode::getState).toList());

        arg.markForReExpansion(root);
        assertEquals(0, builder.expand(root, prec).size());
        assertEquals(Set.of(a, b), exploredActionsLog.get(2));
    }
}
