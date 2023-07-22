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
package hu.bme.mit.theta.analysis.algorithm.lazy.itp;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.InvTransFunc;
import hu.bme.mit.theta.analysis.Lattice;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.algorithm.lazy.LazyState;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.core.utils.Lens;

import java.util.Collection;

import static com.google.common.base.Preconditions.checkNotNull;

public abstract class BinItpStrategy<SConcr extends State, SAbstr extends ExprState, SItp extends State, S extends State, A extends Action, P extends Prec>
        extends ItpStrategy<SConcr, SAbstr, S, A> {

    protected final Interpolator<SAbstr, SItp> interpolator;
    protected final InvTransFunc<SItp, A, P> invTransFunc;
    protected final P prec;

    protected BinItpStrategy(final Lens<S, LazyState<SConcr, SAbstr>> lens,
                             final Lattice<SAbstr> abstrLattice,
                             final Concretizer<SConcr, SAbstr> concretizer,
                             final Interpolator<SAbstr, SItp> interpolator,
                             final InvTransFunc<SItp, A, P> invTransFunc,
                             final P prec) {
        super(lens, abstrLattice, concretizer);
        this.interpolator = checkNotNull(interpolator);
        this.invTransFunc = checkNotNull(invTransFunc);
        this.prec = prec;
    }

    @Override
    public final void cover(final ArgNode<S, A> coveree, final ArgNode<S, A> coverer, final Collection<ArgNode<S, A>> uncoveredNodes) {
        final SItp covererState = interpolator.toItpDom(lens.get(coverer.getState()).getAbstrState());
        final Collection<SItp> complementState = interpolator.complement(covererState);
        complementState.forEach(B -> block(coveree, B, uncoveredNodes));
    }

    @Override
    public final void disable(final ArgNode<S, A> node, final A action, final S succState, final Collection<ArgNode<S, A>> uncoveredNodes) {
        assert inconsistentState(lens.get(succState).getConcrState());
        final SItp top = interpolator.toItpDom(abstrLattice.top());
        final Collection<? extends SItp> badStates = invTransFunc.getPreStates(top, action, prec);
        badStates.forEach(B -> block(node, B, uncoveredNodes));
    }

    protected abstract SAbstr block(final ArgNode<S, A> node, final SItp B, final Collection<ArgNode<S, A>> uncoveredNodes);

}
