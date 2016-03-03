package hu.bme.mit.inf.ttmc.program.tcfa;

import java.util.List;

import hu.bme.mit.inf.ttmc.program.stmt.Stmt;

public interface TCFAEdge {
	
	public TCFA getCFA();
	public TCFALoc getSource();
	public TCFALoc getTarget();
	public List<Stmt> getStmts();

}
