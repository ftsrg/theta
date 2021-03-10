package hu.bme.mit.theta.analysis;

import hu.bme.mit.theta.core.stmt.Stmt;

public interface StmtUnroller<S extends State>{

	Stmt unrollStmt(final S state, final Stmt stmt);

}
