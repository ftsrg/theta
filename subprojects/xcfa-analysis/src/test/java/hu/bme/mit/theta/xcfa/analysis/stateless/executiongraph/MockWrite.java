package hu.bme.mit.theta.xcfa.analysis.stateless.executiongraph;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.Process;
import hu.bme.mit.theta.mcm.graphfilter.interfaces.Write;

public class MockWrite implements Write {
    @Override
    public Process getProcess() {
        return null;
    }

    @Override
    public VarDecl<?> getGlobalVariable() {
        return null;
    }
}
