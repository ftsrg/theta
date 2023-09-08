package hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression;

import hu.bme.mit.delta.collections.IntObjMapView;
import hu.bme.mit.delta.collections.impl.IntObjMapViews;
import hu.bme.mit.delta.java.mdd.MddHandle;
import hu.bme.mit.theta.analysis.algorithm.symbolic.model.AbstractNextStateDescriptor;
import hu.bme.mit.theta.analysis.algorithm.symbolic.model.StateSpaceInfo;

public class MddNodeInitializer implements AbstractNextStateDescriptor.Postcondition {

    private final MddHandle node;

    public MddNodeInitializer(final MddHandle node) {
        this.node = node;
    }

    @Override
    public boolean evaluate() {
        return !node.isTerminalZero();
    }

    @Override
    public IntObjMapView<AbstractNextStateDescriptor> getValuations(StateSpaceInfo localStateSpace) {
        return new IntObjMapViews.Transforming<>(node, n -> new MddNodeInitializer((MddHandle) n));
    }
}
