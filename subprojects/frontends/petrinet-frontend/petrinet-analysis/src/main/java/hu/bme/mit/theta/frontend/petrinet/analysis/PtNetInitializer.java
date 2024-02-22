package hu.bme.mit.theta.frontend.petrinet.analysis;

import hu.bme.mit.delta.collections.IntObjMapView;
import hu.bme.mit.theta.analysis.algorithm.symbolic.model.AbstractNextStateDescriptor;
import hu.bme.mit.theta.analysis.algorithm.symbolic.model.StateSpaceInfo;
import hu.bme.mit.theta.frontend.petrinet.model.Place;

public final class PtNetInitializer implements AbstractNextStateDescriptor.Postcondition {
    private Place assignedPlace;
    private int initialMarking;
    private AbstractNextStateDescriptor continuation;

    public PtNetInitializer(
            final Place assignedPlace, final int initialMarking, final AbstractNextStateDescriptor continuation
    ) {
        this.assignedPlace = assignedPlace;
        this.initialMarking = initialMarking;
        this.continuation = continuation;
    }

    @Override
    public IntObjMapView<AbstractNextStateDescriptor> getValuations(final StateSpaceInfo localStateSpace) {
        if (assignedPlace == localStateSpace.getTraceInfo()) {
            return IntObjMapView.singleton(initialMarking, continuation);
        } else {
            return IntObjMapView.empty(continuation);
        }
    }
}
