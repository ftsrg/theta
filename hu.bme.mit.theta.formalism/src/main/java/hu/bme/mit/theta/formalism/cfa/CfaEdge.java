package hu.bme.mit.theta.formalism.cfa;

import java.util.List;

import hu.bme.mit.theta.formalism.common.Edge;
import hu.bme.mit.theta.formalism.common.stmt.Stmt;

public interface CfaEdge extends Edge<CfaLoc, CfaEdge> {

	public List<Stmt> getStmts();

}
