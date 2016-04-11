package hu.bme.mit.inf.ttmc.formalism.tcfa;

import java.util.List;

import hu.bme.mit.inf.ttmc.formalism.common.Edge;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.Stmt;

public interface TCFAEdge extends Edge<TCFALoc, TCFAEdge> {

	public List<Stmt> getStmts();

}
