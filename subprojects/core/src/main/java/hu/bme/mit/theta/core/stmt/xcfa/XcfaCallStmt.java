package hu.bme.mit.theta.core.stmt.xcfa;

import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.stmt.StmtVisitor;

public class XcfaCallStmt implements Stmt {
    @Override
    public <P, R> R accept(StmtVisitor<? super P, ? extends R> visitor, P param) {
        return visitor.visit(this, param);
    }
}
