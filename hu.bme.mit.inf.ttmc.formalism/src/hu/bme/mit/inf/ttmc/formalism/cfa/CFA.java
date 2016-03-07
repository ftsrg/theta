package hu.bme.mit.inf.ttmc.formalism.cfa;

import java.util.Collection;

public interface CFA {
	
	public CFALoc getInitLoc();
	public CFALoc getFinalLoc();
	public CFALoc getErrorLoc();
	
	public Collection<? extends CFALoc> getLocs();
	public Collection<? extends CFAEdge> getEdges();

}