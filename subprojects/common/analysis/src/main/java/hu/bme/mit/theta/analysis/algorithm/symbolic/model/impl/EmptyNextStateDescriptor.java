package hu.bme.mit.theta.analysis.algorithm.symbolic.model.impl;

import java.util.Optional;

import hu.bme.mit.delta.collections.IntObjMapView;
import hu.bme.mit.theta.analysis.algorithm.symbolic.model.AbstractNextStateDescriptor;
import hu.bme.mit.theta.analysis.algorithm.symbolic.model.RecursiveAbstractNextStateDescriptor;
import hu.bme.mit.theta.analysis.algorithm.symbolic.model.StateSpaceInfo;

public final class EmptyNextStateDescriptor implements RecursiveAbstractNextStateDescriptor {
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

	@Override
	public Cursor cursor(int from) {
		throw new UnsupportedOperationException("Not yet implemented");
	}
}
