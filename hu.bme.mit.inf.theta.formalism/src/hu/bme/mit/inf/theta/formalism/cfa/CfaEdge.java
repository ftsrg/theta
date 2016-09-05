package hu.bme.mit.inf.theta.formalism.cfa;

import java.util.List;

import hu.bme.mit.inf.theta.formalism.common.automaton.Edge;
import hu.bme.mit.inf.theta.formalism.common.stmt.Stmt;

public interface CfaEdge extends Edge<CfaLoc, CfaEdge> {

	public List<Stmt> getStmts();

}
