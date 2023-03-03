package hu.bme.mit.theta.analysis.algorithm.symbolic.symbolicnode.expression;

import hu.bme.mit.delta.collections.IntObjMapView;
import hu.bme.mit.delta.collections.impl.IntObjMapViews;
import hu.bme.mit.delta.mdd.MddHandle;
import hu.bme.mit.theta.analysis.algorithm.symbolic.model.AbstractNextStateDescriptor;
import hu.bme.mit.theta.analysis.algorithm.symbolic.model.StateSpaceInfo;

public class MddNodeNextStateDescriptor implements AbstractNextStateDescriptor {

    private final MddHandle node;

    public MddNodeNextStateDescriptor(MddHandle node) {
        this.node = node;
    }

    @Override
    public boolean evaluate() {
        return !node.isTerminalZero();
    }

    @Override
    public IntObjMapView<AbstractNextStateDescriptor> getDiagonal(StateSpaceInfo localStateSpace) {
        return new IntObjMapViews.Transforming<MddHandle, AbstractNextStateDescriptor>(node, (n, key) -> new MddNodeNextStateDescriptor(n.get(key)));
    }

    @Override
    public IntObjMapView<IntObjMapView<AbstractNextStateDescriptor>> getOffDiagonal(StateSpaceInfo localStateSpace) {
        return new IntObjMapViews.Transforming<MddHandle, IntObjMapView<AbstractNextStateDescriptor>>(node,
                outerNode -> new IntObjMapViews.Transforming<MddHandle, AbstractNextStateDescriptor>(outerNode, MddNodeNextStateDescriptor::new));
    }
}
