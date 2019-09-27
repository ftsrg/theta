package hu.bme.mit.theta.xcfa.dsl;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.ParentCallStmt;
import hu.bme.mit.theta.xcfa.XCFA;

import java.util.List;

class CallStmt extends ParentCallStmt {
    private final VarDecl<?> var;
    private final boolean isVoid;
    private final XCFA.Process process;
    private final List<VarDecl<?>> params;

    CallStmt(VarDecl<?> var, XCFA.Process process, List<VarDecl<?>> params) {
        this.var = var;
        isVoid = var == null;
        this.process = process;
        this.params = params;
    }

    public boolean isVoid() {
        return isVoid;
    }

    public VarDecl<?> getVar() {
        return var;
    }

    public XCFA.Process getProcess() {
        return process;
    }

    public List<VarDecl<?>> getParams() {
        return params;
    }
}
