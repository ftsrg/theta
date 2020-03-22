package hu.bme.mit.theta.core.stmt.xcfa;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.StmtVisitor;
import hu.bme.mit.theta.core.stmt.XcfaStmt;

public class UnlockStmt extends XcfaStmt {
    private static final String STMT_LABEL = "unlock";
    private final VarDecl<?> syncVar;

    public UnlockStmt(VarDecl<?> lhs) {
        syncVar = lhs;
    }

    @Override
    public <P, R> R accept(StmtVisitor<? super P, ? extends R> visitor, P param) {
        return visitor.visit(this, param);
    }

    @Override
    public <P, R> R accept(XcfaStmtVisitor<? super P, ? extends R> visitor, P param) {
        return visitor.visit(this, param);
    }

    public VarDecl<?> getSyncVar() {
        return syncVar;
    }

    public String toString() {
        return Utils.lispStringBuilder(STMT_LABEL).add(syncVar.getName()).toString();
    }
}