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

package hu.bme.mit.theta.analysis.algorithm.lazy;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.common.Unit.unit;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.arg.ArgNode;
import hu.bme.mit.theta.analysis.algorithm.lazy.itp.BasicConcretizer;
import hu.bme.mit.theta.analysis.algorithm.lazy.itp.Concretizer;
import hu.bme.mit.theta.core.utils.Lens;
import java.util.Collection;
import java.util.function.Function;

public final class SameAbstractionLazyStrategy<
                SAbstr extends State, S extends State, A extends Action>
        implements LazyStrategy<SAbstr, SAbstr, S, A> {

    private final Lens<S, SAbstr> lens;
    private final PartialOrd<SAbstr> partialOrd;
    private final Concretizer<SAbstr, SAbstr> concretizer;
    private final Function<S, ?> projection;
    private final InitAbstractor<SAbstr, SAbstr> initAbstractor;

    public SameAbstractionLazyStrategy(
            final Lens<S, SAbstr> lens, final PartialOrd<SAbstr> partialOrd) {
        this.lens = checkNotNull(lens);
        this.partialOrd = checkNotNull(partialOrd);
        projection = s -> unit();
        concretizer = BasicConcretizer.create(partialOrd);
        initAbstractor = s -> s;
    }

    @Override
    public Function<S, ?> getProjection() {
        return projection;
    }

    @Override
    public InitAbstractor<SAbstr, SAbstr> getInitAbstractor() {
        return initAbstractor;
    }

    @Override
    public PartialOrd<SAbstr> getPartialOrd() {
        return partialOrd;
    }

    @Override
    public boolean inconsistentState(final SAbstr state) {
        return concretizer.inconsistentConcrState(state);
    }

    @Override
    public boolean mightCover(final ArgNode<S, A> coveree, final ArgNode<S, A> coverer) {
        return lens.get(coveree.getState()).equals(lens.get(coverer.getState()))
                || concretizer.proves(lens.get(coveree.getState()), lens.get(coverer.getState()));
    }

    @Override
    public void cover(
            final ArgNode<S, A> coveree,
            final ArgNode<S, A> coverer,
            final Collection<ArgNode<S, A>> uncoveredNodes,
            final LazyStatistics.Builder stats) {}

    @Override
    public void disable(
            final ArgNode<S, A> node,
            final A action,
            final S succState,
            final Collection<ArgNode<S, A>> uncoveredNodes,
            final LazyStatistics.Builder stats) {
        assert lens.get(succState).isBottom();
    }
}
