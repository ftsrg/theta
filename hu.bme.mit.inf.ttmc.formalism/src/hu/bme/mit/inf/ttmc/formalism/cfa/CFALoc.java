package hu.bme.mit.inf.ttmc.formalism.cfa;

import java.util.Collection;

public interface CFALoc {

	public Collection<? extends CFAEdge> getInEdges();
	public Collection<? extends CFAEdge> getOutEdges();

}
