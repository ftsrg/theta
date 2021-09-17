package hu.bme.mit.theta.analysis.stmtoptimizer;

import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.core.stmt.Stmt;

public interface StmtOptimizer<S extends State>{

	Stmt optimizeStmt(final S state, final Stmt stmt);

}
