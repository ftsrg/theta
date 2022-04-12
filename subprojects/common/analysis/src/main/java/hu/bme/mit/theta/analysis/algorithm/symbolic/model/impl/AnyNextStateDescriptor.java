package hu.bme.mit.theta.analysis.algorithm.symbolic.model.impl;

import java.util.Optional;

import hu.bme.mit.delta.collections.IntObjMapView;
import hu.bme.mit.delta.collections.UniqueTable;
import hu.bme.mit.theta.analysis.algorithm.symbolic.model.AbstractNextStateDescriptor;
import hu.bme.mit.theta.analysis.algorithm.symbolic.model.StateSpaceInfo;

public class AnyNextStateDescriptor implements AbstractNextStateDescriptor {
	private static final UniqueTable<AnyNextStateDescriptor> uniqueTable = UniqueTable.newInstance();
	
	public static AbstractNextStateDescriptor withChild(AbstractNextStateDescriptor child) {
		return uniqueTable.checkIn(new AnyNextStateDescriptor(child));
	}
	
	private final AbstractNextStateDescriptor child;
	
	private AnyNextStateDescriptor(AbstractNextStateDescriptor child) {
        this.child = child;
    }
	
	@Override
	public boolean isNextStateDefined() {
		return false;
	}
	
	@Override
	public IntObjMapView<AbstractNextStateDescriptor> getDiagonal(StateSpaceInfo localStateSpace) {
		return IntObjMapView.empty(child);
	}
	
	@Override
	public IntObjMapView<IntObjMapView<AbstractNextStateDescriptor>> getOffDiagonal(
			final StateSpaceInfo localStateSpace) {
		return IntObjMapView.empty(IntObjMapView.empty(child));
	}
	
	@Override
	public Optional<Iterable<AbstractNextStateDescriptor>> split() {
		// TODO: this might be a performance overhead
		return Optional.empty();
	}
	
}
