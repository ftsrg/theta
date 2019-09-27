package hu.bme.mit.theta.core.stmt;

import hu.bme.mit.theta.core.stmt.xcfa.XcfaStmtVisitor;

public abstract class XcfaStmt implements Stmt {
    @Override
    public <P, R> R accept(StmtVisitor<? super P, ? extends R> visitor, P param) {
        return visitor.visit(this, param);
    }

    public abstract <P, R> R accept(XcfaStmtVisitor<? super P, ? extends R> visitor, P param);
}