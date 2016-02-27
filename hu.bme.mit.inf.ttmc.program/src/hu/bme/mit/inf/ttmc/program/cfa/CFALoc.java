package hu.bme.mit.inf.ttmc.program.cfa;

import java.util.Collection;

public interface CFALoc {

	public CFA getCFA();
	public Collection<CFAEdge> getInEdges();
	public Collection<CFAEdge> getOutEdges();

}
