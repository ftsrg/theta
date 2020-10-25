package hu.bme.mit.theta.xcfa.analysis.stateless.executiongraph;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.Fence;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.Process;

public class MockFence implements Fence {
    @Override
    public Process getProcess() {
        return null;
    }

    @Override
    public VarDecl<?> getGlobalVariable() {
        return null;
    }
}
