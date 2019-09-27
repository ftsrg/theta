package hu.bme.mit.theta.core.stmt.xcfa;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.StmtVisitor;
import hu.bme.mit.theta.core.stmt.XcfaStmt;

public class NotifyStmt extends XcfaStmt {
    private final VarDecl<?> syncVar;

    public NotifyStmt(VarDecl<?> lhs) {
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
}
