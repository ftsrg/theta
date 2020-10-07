package hu.bme.mit.theta.mcm.graphfilter.interfaces;

import hu.bme.mit.theta.core.decl.VarDecl;

public interface MemoryAccess {
    Process getProcess();
    VarDecl<?> getGlobalVariable();
}
