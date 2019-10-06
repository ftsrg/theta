package hu.bme.mit.theta.xcfa.dsl;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.xcfa.XcfaCallStmt;
import hu.bme.mit.theta.xcfa.XCFA;

import java.util.List;

public class CallStmt extends XcfaCallStmt {
    private final VarDecl<?> var;
    private final boolean isVoid;
    private final XCFA.Process.Procedure procedure;
    private final List<VarDecl<?>> params;

    CallStmt(VarDecl<?> var, XCFA.Process.Procedure procedure, List<VarDecl<?>> params) {
        this.var = var;
        isVoid = var == null;
        this.procedure = procedure;
        this.params = params;
    }

    public boolean isVoid() {
        return isVoid;
    }

    public VarDecl<?> getVar() {
        return var;
    }

    public List<VarDecl<?>> getParams() {
        return params;
    }

    public XCFA.Process.Procedure getProcedure() {
        return procedure;
    }
}
