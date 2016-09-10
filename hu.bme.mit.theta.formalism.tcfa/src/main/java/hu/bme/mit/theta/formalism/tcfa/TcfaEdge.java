package hu.bme.mit.theta.formalism.tcfa;

import java.util.List;

import hu.bme.mit.theta.formalism.common.Edge;
import hu.bme.mit.theta.formalism.common.stmt.Stmt;

public interface TcfaEdge extends Edge<TcfaLoc, TcfaEdge> {

	public List<Stmt> getStmts();

}
