package hu.bme.mit.theta.analysis.prod2.prod2explpred;

import hu.bme.mit.theta.analysis.stmtoptimizer.StmtOptimizer;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.analysis.prod2.Prod2State;
import hu.bme.mit.theta.core.stmt.Stmt;

public class Prod2ExplPredStmtOptimizer implements StmtOptimizer<Prod2State<ExplState, PredState>> {

    private final StmtOptimizer<ExplState> stmtOptimizer;

    private Prod2ExplPredStmtOptimizer(final StmtOptimizer<ExplState> stmtOptimizer) {
        this.stmtOptimizer = stmtOptimizer;
    }

    public static Prod2ExplPredStmtOptimizer create(final StmtOptimizer<ExplState> stmtOptimizer){
        return new Prod2ExplPredStmtOptimizer(stmtOptimizer);
    }

    @Override
    public Stmt optimizeStmt(Prod2State<ExplState, PredState> state, Stmt stmt) {
        return stmtOptimizer.optimizeStmt(state.getState1(),stmt);
    }
}
