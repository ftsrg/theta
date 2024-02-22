package hu.bme.mit.theta.analysis.algorithm.symbolic.model;

import java.util.ArrayList;
import java.util.List;

public interface SymbolicSystem {
    public static SymbolicSystem simpleSystemOf(final List<Component> componentOrder,
                                                final AbstractNextStateDescriptor nextStateDescriptorRoot,
                                                final AbstractNextStateDescriptor initializerDescriptorRoot) {
        return new SymbolicSystem() {
            final List<Component> compOrder = new ArrayList<Component>(componentOrder);

            @Override
            public AbstractNextStateDescriptor getNextStateDescriptorRoot() {
                return nextStateDescriptorRoot;
            }

            @Override
            public AbstractNextStateDescriptor getInitializerDescriptorRoot() {
                return initializerDescriptorRoot;
            }

            @Override
            public List<Component> getComponentOrder() {
                return compOrder;
            }
        };
    }

    public List<Component> getComponentOrder();

    public AbstractNextStateDescriptor getNextStateDescriptorRoot();

    public AbstractNextStateDescriptor getInitializerDescriptorRoot();
}
