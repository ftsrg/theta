package hu.bme.mit.theta.xcfa.dsl;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.ParentCallStmt;
import hu.bme.mit.theta.xcfa.XCFA;

import java.util.List;

class CallStmt extends ParentCallStmt {
    CallStmt(VarDecl<?> var, XCFA.Process process, List<VarDecl<?>> params) {
    }
}
