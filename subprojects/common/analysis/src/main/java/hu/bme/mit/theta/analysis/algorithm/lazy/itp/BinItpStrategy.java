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

package hu.bme.mit.theta.analysis.algorithm.lazy.itp;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.InvTransFunc;
import hu.bme.mit.theta.analysis.Lattice;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.arg.ArgNode;
import hu.bme.mit.theta.analysis.algorithm.lazy.LazyState;
import hu.bme.mit.theta.analysis.algorithm.lazy.LazyStatistics;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.core.utils.Lens;
import java.util.Collection;

public abstract class BinItpStrategy<
                SConcr extends State,
                SAbstr extends ExprState,
                SItp extends State,
                S extends State,
                A extends Action,
                P extends Prec>
        extends ItpStrategy<SConcr, SAbstr, S, A> {

    protected final Interpolator<SAbstr, SItp> interpolator;
    protected final InvTransFunc<SItp, A, P> preImage;
    protected final P prec;

    protected BinItpStrategy(
            final Lens<S, LazyState<SConcr, SAbstr>> lens,
            final Lattice<SAbstr> abstrLattice,
            final Concretizer<SConcr, SAbstr> concretizer,
            final Interpolator<SAbstr, SItp> interpolator,
            final InvTransFunc<SItp, A, P> preImage,
            final P prec) {
        super(lens, abstrLattice, concretizer);
        this.interpolator = checkNotNull(interpolator);
        this.preImage = checkNotNull(preImage);
        this.prec = prec;
    }

    @Override
    public final void cover(
            final ArgNode<S, A> coveree,
            final ArgNode<S, A> coverer,
            final Collection<ArgNode<S, A>> uncoveredNodes,
            final LazyStatistics.Builder stats) {
        stats.startCloseRefinement();
        final SItp covererAbstrState =
                interpolator.toItpDom(lens.get(coverer.getState()).getAbstrState());
        final Collection<SItp> nonCoveredAbstrStates = interpolator.complement(covererAbstrState);
        nonCoveredAbstrStates.forEach(
                badAbstrState -> block(coveree, badAbstrState, uncoveredNodes, stats));
        stats.stopCloseRefinement();
    }

    @Override
    public final void disable(
            final ArgNode<S, A> node,
            final A action,
            final S succState,
            final Collection<ArgNode<S, A>> uncoveredNodes,
            final LazyStatistics.Builder stats) {
        assert inconsistentState(lens.get(succState).getConcrState());
        stats.startExpandRefinement();
        final Collection<? extends SItp> abstrStatesWhereActionIsEnabled =
                preImage.getPreStates(interpolator.toItpDom(abstrLattice.top()), action, prec);
        abstrStatesWhereActionIsEnabled.forEach(
                badAbstrState -> block(node, badAbstrState, uncoveredNodes, stats));
        stats.stopExpandRefinement();
    }

    protected abstract SAbstr block(
            final ArgNode<S, A> node,
            final SItp badState,
            final Collection<ArgNode<S, A>> uncoveredNodes,
            final LazyStatistics.Builder stats);
}
