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

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.arg.ArgNode;
import hu.bme.mit.theta.analysis.algorithm.lazy.itp.Concretizer;
import hu.bme.mit.theta.core.utils.Lens;
import java.util.Collection;
import java.util.function.Function;

public final class IdentityAbstractionLazyStrategy<
                SConcr extends State, S extends State, A extends Action>
        implements LazyStrategy<SConcr, SConcr, S, A> {

    private final Lens<S, SConcr> lens;
    private final PartialOrd<SConcr> partialOrd;
    private final Function<S, SConcr> projection;
    private final Concretizer<SConcr, SConcr> concretizer;
    private final InitAbstractor<SConcr, SConcr> initAbstractor;

    public IdentityAbstractionLazyStrategy(
            final Lens<S, SConcr> lens, final Concretizer<SConcr, SConcr> concretizer) {
        this.lens = checkNotNull(lens);
        this.concretizer = checkNotNull(concretizer);
        partialOrd = (s1, s2) -> s1.isBottom() || s1.equals(s2);
        projection = s -> lens.get(s);
        initAbstractor = s -> s;
    }

    @Override
    public final Function<S, SConcr> getProjection() {
        return projection;
    }

    @Override
    public InitAbstractor<SConcr, SConcr> getInitAbstractor() {
        return initAbstractor;
    }

    @Override
    public PartialOrd<SConcr> getPartialOrd() {
        return partialOrd;
    }

    @Override
    public boolean inconsistentState(final SConcr state) {
        return concretizer.inconsistentConcrState(state);
    }

    @Override
    public final boolean mightCover(final ArgNode<S, A> coveree, final ArgNode<S, A> coverer) {
        assert lens.get(coveree.getState()).equals(lens.get(coverer.getState()));
        return true;
    }

    @Override
    public final void cover(
            final ArgNode<S, A> coveree,
            final ArgNode<S, A> coverer,
            final Collection<ArgNode<S, A>> uncoveredNodes,
            final LazyStatistics.Builder stats) {}

    @Override
    public final void disable(
            final ArgNode<S, A> node,
            final A action,
            final S succState,
            final Collection<ArgNode<S, A>> uncoveredNodes,
            final LazyStatistics.Builder stats) {
        assert lens.get(succState).isBottom();
    }
}
