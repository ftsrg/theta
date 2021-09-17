package hu.bme.mit.theta.analysis.expl;

import hu.bme.mit.theta.analysis.stmtoptimizer.StmtOptimizer;
import hu.bme.mit.theta.analysis.stmtoptimizer.StmtSimplifier;
import hu.bme.mit.theta.core.stmt.Stmt;

public class ExplStmtOptimizer implements StmtOptimizer<ExplState> {

    private ExplStmtOptimizer(){}

    private static class LazyHolder {
        static final ExplStmtOptimizer INSTANCE = new ExplStmtOptimizer();
    }

    public static ExplStmtOptimizer getInstance() {
        return LazyHolder.INSTANCE;
    }

    @Override
    public Stmt optimizeStmt(final ExplState state, final Stmt stmt) {
        return StmtSimplifier.simplifyStmt(state,stmt);
    }
}
