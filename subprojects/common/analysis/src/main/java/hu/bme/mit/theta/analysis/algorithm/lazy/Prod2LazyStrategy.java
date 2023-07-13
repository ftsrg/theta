/*
 *  Copyright 2023 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.analysis.algorithm.lazy;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.core.utils.Lens;
import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.prod2.Prod2Ord;
import hu.bme.mit.theta.analysis.prod2.Prod2State;

import java.util.Collection;
import java.util.function.Function;

import static com.google.common.base.Preconditions.checkNotNull;

public final class Prod2LazyStrategy<SConcr1 extends State, SConcr2 extends State, SAbstr1 extends State, SAbstr2 extends State, S extends State, A extends Action> implements LazyStrategy<Prod2State<SConcr1, SConcr2>, Prod2State<SAbstr1, SAbstr2>, S, A> {

    private final Lens<S, Prod2State<SConcr1, SConcr2>> lens;
    private final LazyStrategy<SConcr1, SAbstr1, S, A> strategy1;
    private final LazyStrategy<SConcr2, SAbstr2, S, A> strategy2;
    private final Function<S, ?> projection;
    private final InitAbstractor<Prod2State<SConcr1, SConcr2>, Prod2State<SAbstr1, SAbstr2>> initAbstractor;
    private final PartialOrd<Prod2State<SAbstr1, SAbstr2>> partialOrd;

    public Prod2LazyStrategy(final Lens<S, Prod2State<SConcr1, SConcr2>> lens,
                             final LazyStrategy<SConcr1, SAbstr1, S, A> strategy1,
                             final LazyStrategy<SConcr2, SAbstr2, S, A> strategy2,
                             final Function<S, ?> projection) {
        this.lens = checkNotNull(lens);
        this.strategy1 = checkNotNull(strategy1);
        this.strategy2 = checkNotNull(strategy2);
        this.projection = checkNotNull(projection);
        initAbstractor = s -> Prod2State.of(
                strategy1.getInitAbstractor().getInitAbstrState(s.getState1()),
                strategy2.getInitAbstractor().getInitAbstrState(s.getState2()));
        partialOrd = Prod2Ord.create(strategy1.getPartialOrd(), strategy2.getPartialOrd());
    }

    @Override
    public Function<S, ?> getProjection() {
        return projection;
    }

    @Override
    public InitAbstractor<Prod2State<SConcr1, SConcr2>, Prod2State<SAbstr1, SAbstr2>> getInitAbstractor() {
        return initAbstractor;
    }

    @Override
    public PartialOrd<Prod2State<SAbstr1, SAbstr2>> getPartialOrd() {
        return partialOrd;
    }

    @Override
    public boolean inconsistentState(Prod2State<SConcr1, SConcr2> state) {
        return state.isBottom() ||
                strategy1.inconsistentState(state.getState1()) || strategy2.inconsistentState(state.getState2());
    }

    @Override
    public boolean mightCover(ArgNode<S, A> coveree, ArgNode<S, A> coverer) {
        return strategy1.mightCover(coveree, coverer) && strategy2.mightCover(coveree, coverer);
    }

    @Override
    public void cover(ArgNode<S, A> coveree, ArgNode<S, A> coverer, Collection<ArgNode<S, A>> uncoveredNodes) {
        assert coveree.getCoveringNode().isPresent() && coveree.getCoveringNode().get().equals(coverer);
        strategy1.cover(coveree, coverer, uncoveredNodes);
        if (coveree.isCovered()) {
            assert (!uncoveredNodes.contains(coveree));
            strategy2.cover(coveree, coverer, uncoveredNodes);
        }
    }

    @Override
    public void disable(ArgNode<S, A> node, A action, S succState, Collection<ArgNode<S, A>> uncoveredNodes) {
        Prod2State<SConcr1, SConcr2> state = lens.get(succState);
        assert inconsistentState(state);
        if (state.isBottom1() || (!state.isBottom2() && strategy1.inconsistentState(state.getState1()))) {
            strategy1.disable(node, action, succState, uncoveredNodes);
        } else if (strategy2.inconsistentState(state.getState2())) {
            strategy2.disable(node, action, succState, uncoveredNodes);
        } else {
            throw new AssertionError();
        }
    }
}
