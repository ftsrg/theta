package hu.bme.mit.inf.ttmc.program.cfa;

import java.util.List;

import hu.bme.mit.inf.ttmc.program.stmt.Stmt;

public interface CFAEdge {
	
	public CFA getCFA();
	public CFALoc getSource();
	public CFALoc getTarget();
	public List<Stmt> getStmts();

}
