package hu.bme.mit.theta.core.stmt;

public final class DelayStmt implements Stmt {

    private static final int HASH_CODE = 6117589;
    private static final String STMT_LABEL = "delay";

    private DelayStmt() {}

    private static class LazyHolder {
        static final DelayStmt INSTANCE = new DelayStmt();
    }

    public static DelayStmt getInstance() {
        return DelayStmt.LazyHolder.INSTANCE;
    }

    @Override
    public <P, R> R accept(StmtVisitor<? super P, ? extends R> visitor, P param) {
        return visitor.visit(this, param);
    }

    @Override
    public int hashCode() {
        return HASH_CODE;
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj == null) {
            return false;
        } else {
            return this.getClass() == obj.getClass();
        }
    }

    @Override
    public String toString() {
        return STMT_LABEL;
    }
}
