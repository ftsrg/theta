package hu.bme.mit.inf.ttmc.formalism.tcfa;

import java.util.List;

import hu.bme.mit.inf.ttmc.formalism.common.automaton.Edge;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.Stmt;

public interface TcfaEdge extends Edge<TcfaLoc, TcfaEdge> {

	public List<Stmt> getStmts();

}
