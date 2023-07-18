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
import hu.bme.mit.theta.analysis.algorithm.ArgEdge;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.algorithm.lazy.LazyState;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.core.utils.Lens;

import java.util.Collection;

public final class BwItpStrategy<SConcr extends State, SAbstr extends ExprState, SItp extends State, S extends State, A extends Action, P extends Prec>
        extends BinItpStrategy<SConcr, SAbstr, SItp, S, A, P> {

    public BwItpStrategy(final Lens<S, LazyState<SConcr, SAbstr>> lens,
                         final Lattice<SAbstr> abstrLattice,
                         final Interpolator<SAbstr, SItp> interpolator,
                         final Concretizer<SConcr, SAbstr> concretizer,
                         final InvTransFunc<SItp, A, P> invTransFunc,
                         final P prec) {
        super(lens, abstrLattice, concretizer, interpolator, invTransFunc, prec);
    }

    @Override
    public final SAbstr block(final ArgNode<S, A> node, final SItp B, final Collection<ArgNode<S, A>> uncoveredNodes) {

        final SAbstr abstrState = lens.get(node.getState()).getAbstrState();
        if (interpolator.refutes(abstrState, B)) {
            return abstrState;
        }

        final SConcr concrState = lens.get(node.getState()).getConcrState();
        final SAbstr interpolant = interpolator.interpolate(concretizer.concretize(concrState), B);

        strengthen(node, interpolant);
        maintainCoverage(node, interpolant, uncoveredNodes);

        if (node.getInEdge().isPresent()) {
            final ArgEdge<S, A> inEdge = node.getInEdge().get();
            final A action = inEdge.getAction();
            final ArgNode<S, A> parent = inEdge.getSource();

            final Collection<SItp> badStates = interpolator.complement(interpolator.toItpDom(interpolant));
            for (final SItp badState : badStates) {
                final Collection<? extends SItp> preBadStates = invTransFunc.getPreStates(badState, action, prec);
                for (final SItp preBadState : preBadStates) {
                    block(parent, preBadState, uncoveredNodes);
                }
            }
        }

        return interpolant;
    }

}
