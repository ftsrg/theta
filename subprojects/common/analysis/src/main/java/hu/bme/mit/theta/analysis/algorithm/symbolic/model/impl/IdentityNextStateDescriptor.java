package hu.bme.mit.theta.analysis.algorithm.symbolic.model.impl;

import java.util.Optional;

import hu.bme.mit.delta.collections.IntObjMapView;
import hu.bme.mit.delta.collections.UniqueTable;
import hu.bme.mit.theta.analysis.algorithm.symbolic.model.AbstractNextStateDescriptor;
import hu.bme.mit.theta.analysis.algorithm.symbolic.model.StateSpaceInfo;

public final class IdentityNextStateDescriptor implements AbstractNextStateDescriptor {
    private static final UniqueTable<IdentityNextStateDescriptor> uniqueTable = UniqueTable.newInstance();

    public static final AbstractNextStateDescriptor TERMINAL_IDENTITY = new IdentityNextStateDescriptor();

    public static AbstractNextStateDescriptor withChild(AbstractNextStateDescriptor child) {
        return uniqueTable.checkIn(new IdentityNextStateDescriptor(child));
    }

    private final AbstractNextStateDescriptor child;

    private IdentityNextStateDescriptor(AbstractNextStateDescriptor child) {
        this.child = child;
    }

    private IdentityNextStateDescriptor() {
        this.child = this;
    }

    @Override
    public IntObjMapView<AbstractNextStateDescriptor> getDiagonal(StateSpaceInfo localStateSpace) {
        // TODO: cache this instead of creating on demand
        return IntObjMapView.empty(child);
    }

    @Override
    public IntObjMapView<IntObjMapView<AbstractNextStateDescriptor>> getOffDiagonal(
            StateSpaceInfo localStateSpace) {
        // TODO: cache this instead of creating on demand
        return IntObjMapView.empty(IntObjMapView.empty(AbstractNextStateDescriptor.terminalEmpty()));
    }

    @Override
    public Optional<Iterable<AbstractNextStateDescriptor>> split() {
        // TODO: this might be a performance overhead
        return Optional.empty();
    }

    @Override
    public boolean evaluate() {
        return true;
    }
}
