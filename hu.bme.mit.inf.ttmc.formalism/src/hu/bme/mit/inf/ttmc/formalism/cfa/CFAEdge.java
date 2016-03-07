package hu.bme.mit.inf.ttmc.formalism.cfa;

import java.util.List;

import hu.bme.mit.inf.ttmc.formalism.stmt.Stmt;

public interface CFAEdge {

	public CFALoc getSource();
	public CFALoc getTarget();
	public List<Stmt> getStmts();

}
