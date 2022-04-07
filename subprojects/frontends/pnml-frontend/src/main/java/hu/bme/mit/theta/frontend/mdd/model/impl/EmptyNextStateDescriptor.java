package hu.bme.mit.theta.frontend.mdd.model.impl;

import java.util.Optional;

import hu.bme.mit.delta.collections.IntObjMapView;
import hu.bme.mit.theta.frontend.mdd.model.AbstractNextStateDescriptor;
import hu.bme.mit.theta.frontend.mdd.model.StateSpaceInfo;

public final class EmptyNextStateDescriptor implements AbstractNextStateDescriptor {
	private EmptyNextStateDescriptor() {}
	
	public static final EmptyNextStateDescriptor INSTANCE = new EmptyNextStateDescriptor();
	
	@Override
	public IntObjMapView<AbstractNextStateDescriptor> getDiagonal(StateSpaceInfo localStateSpace) {
		// TODO: cache this instead of creating on demand
		return IntObjMapView.empty(INSTANCE);
	}
	
	@Override
	public IntObjMapView<IntObjMapView<AbstractNextStateDescriptor>> getOffDiagonal(
			StateSpaceInfo localStateSpace) {
		// TODO: cache this instead of creating on demand
		return IntObjMapView.empty(IntObjMapView.empty(INSTANCE));
	}

	@Override
	public Optional<Iterable<AbstractNextStateDescriptor>> split() {
		return Optional.empty();
	}
	
	@Override
	public boolean evaluate() {
		return false;
	}
}
