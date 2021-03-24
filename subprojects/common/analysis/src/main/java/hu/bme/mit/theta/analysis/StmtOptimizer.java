package hu.bme.mit.theta.analysis;

import hu.bme.mit.theta.core.stmt.Stmt;

public interface StmtOptimizer<S extends State>{

	Stmt optimizeStmt(final S state, final Stmt stmt);

}
