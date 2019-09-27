package hu.bme.mit.theta.core.stmt;

public class ParentCallStmt implements Stmt {
    @Override
    public <P, R> R accept(StmtVisitor<? super P, ? extends R> visitor, P param) {
        return null;
    }
}
