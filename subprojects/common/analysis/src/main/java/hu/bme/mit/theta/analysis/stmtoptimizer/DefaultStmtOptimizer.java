package hu.bme.mit.theta.analysis.stmtoptimizer;

import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.core.stmt.Stmt;

public class DefaultStmtOptimizer<S extends State> implements StmtOptimizer<S> {

    public static <S extends State> DefaultStmtOptimizer<S> create() {
        return new DefaultStmtOptimizer<>();
    }

    @Override
    public Stmt optimizeStmt(S state, Stmt stmt) {
        return stmt;
    }

}
