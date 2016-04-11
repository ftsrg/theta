package hu.bme.mit.inf.ttmc.formalism.cfa;

import java.util.List;

import hu.bme.mit.inf.ttmc.formalism.common.Edge;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.Stmt;

public interface CFAEdge extends Edge<CFALoc, CFAEdge> {

	public List<Stmt> getStmts();

}
