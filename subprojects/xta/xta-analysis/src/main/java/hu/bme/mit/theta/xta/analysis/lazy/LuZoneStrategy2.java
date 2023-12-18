package hu.bme.mit.theta.xta.analysis.lazy;

import hu.bme.mit.theta.core.utils.Lens;
import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ArgEdge;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.algorithm.lazy.LazyStrategy;
import hu.bme.mit.theta.analysis.algorithm.lazy.InitAbstractor;
import hu.bme.mit.theta.analysis.zone.BoundFunc;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.xta.analysis.XtaAction;
import hu.bme.mit.theta.xta.analysis.zone.XtaLuZoneUtils;
import hu.bme.mit.theta.xta.analysis.zone.lu.LuZoneOrd;
import hu.bme.mit.theta.xta.analysis.zone.lu.LuZoneState;

import java.util.Collection;
import java.util.function.Function;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.common.Unit.unit;
import static java.util.stream.Collectors.toList;

public final class LuZoneStrategy2<S extends State> implements LazyStrategy<ZoneState, LuZoneState, S, XtaAction> {

    private final Lens<S, LuZoneState> lens;
    private final Function<S, ?> projection;
    private final InitAbstractor<ZoneState, LuZoneState> initAbstractor;
    private final PartialOrd<LuZoneState> partialOrd;

    public LuZoneStrategy2(Lens<S, LuZoneState> lens) {
        this.lens = checkNotNull(lens);
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
    public boolean inconsistentState(S state) {
        return lens.get(state).isBottom();
    }

    @Override
    public boolean mightCover(ArgNode<S, XtaAction> coveree, ArgNode<S, XtaAction> coverer) {
        final LuZoneState covereeState = lens.get(coveree.getState());
        final LuZoneState covererState = lens.get(coverer.getState());
        return covereeState.getZone().isLeq(covererState.getZone(), covererState.getBoundFunc());
    }

    @Override
    public void cover(ArgNode<S, XtaAction> coveree, ArgNode<S, XtaAction> coverer, Collection<ArgNode<S, XtaAction>> uncoveredNodes) {
        final LuZoneState covererState = lens.get(coverer.getState());
        final BoundFunc boundFunc = covererState.getBoundFunc();
        propagateBounds(coveree, boundFunc, uncoveredNodes);
    }

    @Override
    public void disable(ArgNode<S, XtaAction> node, XtaAction action, S succState, Collection<ArgNode<S, XtaAction>> uncoveredNodes) {
        assert succState.isBottom();
        final BoundFunc preImage = XtaLuZoneUtils.pre(BoundFunc.top(), action);
        propagateBounds(node, preImage, uncoveredNodes);
    }

    private void propagateBounds(final ArgNode<S, XtaAction> node, final BoundFunc boundFunc, final Collection<ArgNode<S, XtaAction>> uncoveredNodes) {
        final LuZoneState oldState = lens.get(node.getState());
        final BoundFunc oldBoundFunc = oldState.getBoundFunc();
        if (!boundFunc.isLeq(oldBoundFunc)) {

            strengthen(node, boundFunc);
            maintainCoverage(node, boundFunc, uncoveredNodes);

            if (node.getInEdge().isPresent()) {
                final ArgEdge<S, XtaAction> inEdge = node.getInEdge().get();
                final XtaAction action = inEdge.getAction();
                final ArgNode<S, XtaAction> parent = inEdge.getSource();
                final BoundFunc preBound = XtaLuZoneUtils.pre(boundFunc, action);
                propagateBounds(parent, preBound, uncoveredNodes);
            }
        }
    }

    private void strengthen(final ArgNode<S, XtaAction> node, final BoundFunc boundFunc) {
        final S state = node.getState();
        final LuZoneState luZoneState = lens.get(state);
        final BoundFunc oldBoundFunc = luZoneState.getBoundFunc();
        final BoundFunc newBoundFunc = oldBoundFunc.merge(boundFunc);
        final LuZoneState newLuZoneState = luZoneState.withBoundFunc(newBoundFunc);
        final S newState = lens.set(state, newLuZoneState);
        node.setState(newState);
    }

    private void maintainCoverage(final ArgNode<S, XtaAction> node, final BoundFunc interpolant, final Collection<ArgNode<S, XtaAction>> uncoveredNodes) {

        final LuZoneState covererState = lens.get(node.getState());
        final Collection<ArgNode<S, XtaAction>> uncovered = node.getCoveredNodes()
                .filter(covered -> shouldUncover(covered, covererState, interpolant)).collect(toList());
        uncoveredNodes.addAll(uncovered);
        uncovered.forEach(ArgNode::unsetCoveringNode);
    }

    private boolean shouldUncover(final ArgNode<S, XtaAction> covered, final LuZoneState covererState, final BoundFunc interpolant) {
        final LuZoneState coveredState = lens.get(covered.getState());
        return !interpolant.isLeq(coveredState.getBoundFunc())
                || !coveredState.getZone().isLeq(covererState.getZone(), interpolant);
    }

}
