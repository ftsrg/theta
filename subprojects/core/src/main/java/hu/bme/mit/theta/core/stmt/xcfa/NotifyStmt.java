package hu.bme.mit.theta.core.stmt.xcfa;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.stmt.StmtVisitor;

public class NotifyStmt implements Stmt {
    private final VarDecl<?> syncVar;

    public NotifyStmt(VarDecl<?> lhs) {
        syncVar = lhs;
    }

    @Override
    public <P, R> R accept(StmtVisitor<? super P, ? extends R> visitor, P param) {
        return visitor.visit(this, param);
    }

    public VarDecl<?> getSyncVar() {
        return syncVar;
    }
}
