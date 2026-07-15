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
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.algorithm.arg.ArgEdge;
import hu.bme.mit.theta.analysis.algorithm.arg.ArgNode;
import hu.bme.mit.theta.analysis.algorithm.lazy.LazyState;
import hu.bme.mit.theta.analysis.algorithm.lazy.LazyStatistics;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.core.utils.Lens;
import java.util.Collection;

public final class FwItpStrategy<
                SConcr extends State,
                SAbstr extends ExprState,
                SItp extends State,
                S extends State,
                A extends Action,
                P extends Prec,
                PAbstr extends Prec>
        extends BinItpStrategy<SConcr, SAbstr, SItp, S, A, P> {

    private final TransFunc<SAbstr, A, PAbstr> postImage;
    private final PAbstr abstrPrec;

    public FwItpStrategy(
            final Lens<S, LazyState<SConcr, SAbstr>> lens,
            final Lattice<SAbstr> abstrLattice,
            final Interpolator<SAbstr, SItp> interpolator,
            final Concretizer<SConcr, SAbstr> concretizer,
            final InvTransFunc<SItp, A, P> preImage,
            final P prec,
            final TransFunc<SAbstr, A, PAbstr> postImage,
            final PAbstr abstrPrec) {
        super(lens, abstrLattice, concretizer, interpolator, preImage, prec);
        this.postImage = checkNotNull(postImage);
        this.abstrPrec = checkNotNull(abstrPrec);
    }

    @Override
    public SAbstr block(
            final ArgNode<S, A> node,
            final SItp badState,
            final Collection<ArgNode<S, A>> uncoveredNodes,
            final LazyStatistics.Builder stats) {

        final SAbstr abstrState = lens.get(node.getState()).getAbstrState();
        if (interpolator.refutes(abstrState, badState)) {
            return abstrState;
        }
        stats.refine();

        SAbstr interpolant = null;

        if (node.getInEdge().isPresent()) {
            final ArgEdge<S, A> inEdge = node.getInEdge().get();
            final A action = inEdge.getAction();
            final ArgNode<S, A> parent = inEdge.getSource();

            for (final SItp preBadState : preImage.getPreStates(badState, action, prec)) {

                final SAbstr preItp = block(parent, preBadState, uncoveredNodes, stats);

                final Collection<? extends SAbstr> preItpSuccessors =
                        postImage.getSuccStates(preItp, action, abstrPrec);
                assert preItpSuccessors.size() == 1;
                final SAbstr preItpSuccessor = preItpSuccessors.stream().findFirst().get();

                final SAbstr i = interpolator.interpolate(preItpSuccessor, badState);

                if (interpolant == null) {
                    interpolant = i;
                } else {
                    interpolant = abstrLattice.meet(interpolant, i);
                }
            }
        } else {
            final SAbstr rootConcrState =
                    concretizer.concretize(lens.get(node.getState()).getConcrState());
            interpolant = interpolator.interpolate(rootConcrState, badState);
        }

        strengthen(node, interpolant);
        maintainCoverage(node, interpolant, uncoveredNodes);

        return interpolant;
    }
}
