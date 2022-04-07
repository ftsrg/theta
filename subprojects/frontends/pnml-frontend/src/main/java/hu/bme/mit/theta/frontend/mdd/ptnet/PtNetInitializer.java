package hu.bme.mit.theta.frontend.mdd.ptnet;

import hu.bme.mit.delta.collections.IntObjMapView;
import hu.bme.mit.theta.frontend.petrinet.model.Place;
import hu.bme.mit.theta.frontend.mdd.model.AbstractNextStateDescriptor;
import hu.bme.mit.theta.frontend.mdd.model.StateSpaceInfo;

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
