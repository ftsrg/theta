package hu.bme.mit.theta.core.stmt.xcfa;

import hu.bme.mit.theta.core.stmt.XcfaStmt;

public class FenceStmt extends XcfaStmt {
    private final String type;

    public FenceStmt(String type) {
        this.type = type;
    }

    @Override
    public <P, R> R accept(XcfaStmtVisitor<? super P, ? extends R> visitor, P param) {
        return visitor.visit(this, param);
    }

    public String getType() {
        return type;
    }
}
