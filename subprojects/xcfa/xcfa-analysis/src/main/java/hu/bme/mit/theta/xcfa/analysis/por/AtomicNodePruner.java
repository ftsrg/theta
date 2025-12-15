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
package hu.bme.mit.theta.xcfa.analysis.por;

import hu.bme.mit.theta.analysis.algorithm.arg.ARG;
import hu.bme.mit.theta.analysis.algorithm.arg.ArgEdge;
import hu.bme.mit.theta.analysis.algorithm.arg.ArgNode;
import hu.bme.mit.theta.analysis.expr.refinement.NodePruner;
import hu.bme.mit.theta.xcfa.analysis.XcfaAction;
import hu.bme.mit.theta.xcfa.analysis.XcfaState;
import hu.bme.mit.theta.xcfa.model.AtomicFenceLabel;

/**
 * Prunes the given node from the given ARG if the action of its incoming edge is not part of an
 * atomic block. Otherwise, the closest ancestor of the node is pruned for whom the above condition
 * holds.
 *
 * @param <S> {@link XcfaState}
 * @param <A> {@link XcfaAction}
 */
public class AtomicNodePruner<S extends XcfaState<?>, A extends XcfaAction>
        implements NodePruner<S, A> {
    @Override
    public void prune(final ARG<S, A> arg, ArgNode<S, A> node) {
        var atomicMutex = AtomicFenceLabel.Companion.getATOMIC_MUTEX().getName();
        while (node.getState().getMutexes().containsKey(atomicMutex)) {
            ArgEdge<S, A> inEdge = node.getInEdge().get();
            node = inEdge.getSource();
        }
        arg.prune(node);
    }
}
