package hu.bme.mit.theta.core.stmt.xcfa;

import hu.bme.mit.theta.core.stmt.StmtVisitor;
import hu.bme.mit.theta.core.stmt.XcfaStmt;

public class AtomicBeginStmt extends XcfaStmt {
    @Override
    public <P, R> R accept(StmtVisitor<? super P, ? extends R> visitor, P param) {
        return visitor.visit(this, param);
    }

    @Override
    public <P, R> R accept(XcfaStmtVisitor<? super P, ? extends R> visitor, P param) {
        return visitor.visit(this, param);
    }
}
