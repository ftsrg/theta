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

package hu.bme.mit.theta.analysis.algorithm.lazy.lu;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.common.Unit.unit;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.arg.ArgEdge;
import hu.bme.mit.theta.analysis.algorithm.arg.ArgNode;
import hu.bme.mit.theta.analysis.algorithm.lazy.InitAbstractor;
import hu.bme.mit.theta.analysis.algorithm.lazy.LazyStatistics;
import hu.bme.mit.theta.analysis.algorithm.lazy.LazyStrategy;
import hu.bme.mit.theta.analysis.zone.BoundFunc;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.analysis.zone.lu.LuZoneOrd;
import hu.bme.mit.theta.analysis.zone.lu.LuZoneState;
import hu.bme.mit.theta.core.utils.Lens;
import java.util.Collection;
import java.util.function.Function;

public final class LuZoneStrategy<S extends State, A extends Action>
        implements LazyStrategy<ZoneState, LuZoneState, S, A> {

    private final Lens<S, LuZoneState> lens;
    private final Function<S, ?> projection;
    private final InitAbstractor<ZoneState, LuZoneState> initAbstractor;
    private final PartialOrd<LuZoneState> partialOrd;
    private final LuZonePre<A> pre;

    public LuZoneStrategy(final Lens<S, LuZoneState> lens, final LuZonePre<A> pre) {
        this.lens = checkNotNull(lens);
        this.pre = pre;
        projection = s -> unit();
        initAbstractor = s -> LuZoneState.of(s, BoundFunc.top());
        partialOrd = LuZoneOrd.getInstance();
    }

    @Override
    public Function<S, ?> getProjection() {
        return projection;
    }

    @Override
    public InitAbstractor<ZoneState, LuZoneState> getInitAbstractor() {
        return initAbstractor;
    }

    @Override
    public PartialOrd<LuZoneState> getPartialOrd() {
        return partialOrd;
    }

    @Override
    public boolean inconsistentState(final ZoneState state) {
        return state.isBottom();
    }

    @Override
    public boolean mightCover(final ArgNode<S, A> coveree, final ArgNode<S, A> coverer) {
        final LuZoneState covereeState = lens.get(coveree.getState());
        final LuZoneState covererState = lens.get(coverer.getState());
        return covereeState.getZone().isLeq(covererState.getZone(), covererState.getBoundFunc());
    }

    @Override
    public void cover(
            final ArgNode<S, A> coveree,
            final ArgNode<S, A> coverer,
            final Collection<ArgNode<S, A>> uncoveredNodes,
            final LazyStatistics.Builder stats) {
        stats.startCloseRefinement();
        final LuZoneState covererState = lens.get(coverer.getState());
        final BoundFunc boundFunc = covererState.getBoundFunc();
        propagateBounds(coveree, boundFunc, uncoveredNodes, stats);
        stats.stopCloseRefinement();
    }

    @Override
    public void disable(
            final ArgNode<S, A> node,
            final A action,
            final S succState,
            final Collection<ArgNode<S, A>> uncoveredNodes,
            final LazyStatistics.Builder stats) {
        assert succState.isBottom();
        stats.startExpandRefinement();
        final BoundFunc preImage = pre.pre(BoundFunc.top(), action);
        propagateBounds(node, preImage, uncoveredNodes, stats);
        stats.stopExpandRefinement();
    }

    private void propagateBounds(
            final ArgNode<S, A> node,
            final BoundFunc boundFunc,
            final Collection<ArgNode<S, A>> uncoveredNodes,
            final LazyStatistics.Builder stats) {
        final LuZoneState oldState = lens.get(node.getState());
        final BoundFunc oldBoundFunc = oldState.getBoundFunc();
        if (!boundFunc.isLeq(oldBoundFunc)) {
            stats.refine();

            strengthen(node, boundFunc);
            maintainCoverage(node, boundFunc, uncoveredNodes);

            if (node.getInEdge().isPresent()) {
                final ArgEdge<S, A> inEdge = node.getInEdge().get();
                final A action = inEdge.getAction();
                final ArgNode<S, A> parent = inEdge.getSource();
                final BoundFunc preBound = pre.pre(boundFunc, action);
                propagateBounds(parent, preBound, uncoveredNodes, stats);
            }
        }
    }

    private void strengthen(final ArgNode<S, A> node, final BoundFunc boundFunc) {
        final S state = node.getState();
        final LuZoneState luZoneState = lens.get(state);
        final BoundFunc oldBoundFunc = luZoneState.getBoundFunc();
        final BoundFunc newBoundFunc = oldBoundFunc.merge(boundFunc);
        final LuZoneState newLuZoneState = luZoneState.withBoundFunc(newBoundFunc);
        final S newState = lens.set(state, newLuZoneState);
        node.setState(newState);
    }

    private void maintainCoverage(
            final ArgNode<S, A> node,
            final BoundFunc interpolant,
            final Collection<ArgNode<S, A>> uncoveredNodes) {

        final LuZoneState covererState = lens.get(node.getState());
        final Collection<ArgNode<S, A>> uncovered =
                node.getCoveredNodes()
                        .filter(covered -> shouldUncover(covered, covererState, interpolant))
                        .toList();
        uncoveredNodes.addAll(uncovered);
        uncovered.forEach(ArgNode::unsetCoveringNode);
    }

    private boolean shouldUncover(
            final ArgNode<S, A> covered,
            final LuZoneState covererState,
            final BoundFunc interpolant) {
        final LuZoneState coveredState = lens.get(covered.getState());
        return !interpolant.isLeq(coveredState.getBoundFunc())
                || !coveredState.getZone().isLeq(covererState.getZone(), interpolant);
    }
}
