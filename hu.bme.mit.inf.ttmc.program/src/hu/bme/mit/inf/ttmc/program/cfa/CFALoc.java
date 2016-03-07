package hu.bme.mit.inf.ttmc.program.cfa;

import java.util.Collection;

public interface CFALoc {

	public Collection<? extends CFAEdge> getInEdges();
	public Collection<? extends CFAEdge> getOutEdges();

}
