package hu.bme.mit.theta.core.stmt.xcfa;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.StmtVisitor;
import hu.bme.mit.theta.core.stmt.XcfaStmt;

public class LoadStmt extends XcfaStmt {
    private final VarDecl<?> lhs;
    private final VarDecl<?> rhs;
    private final boolean atomic;
    private final String ordering;
    public LoadStmt(VarDecl<?> lhs, VarDecl<?> rhs, boolean atomic, String ordering) {
        this.lhs = lhs;
        this.rhs = rhs;
        this.atomic = atomic;
        this.ordering = ordering;
    }

    @Override
    public <P, R> R accept(StmtVisitor<? super P, ? extends R> visitor, P param) {
        return visitor.visit(this, param);
    }

    @Override
    public <P, R> R accept(XcfaStmtVisitor<? super P, ? extends R> visitor, P param) {
        return visitor.visit(this, param);
    }

    public VarDecl<?> getLhs() {
        return lhs;
    }

    public VarDecl<?> getRhs() {
        return rhs;
    }

    public boolean isAtomic() {
        return atomic;
    }

    public String getOrdering() {
        return ordering;
    }
}
