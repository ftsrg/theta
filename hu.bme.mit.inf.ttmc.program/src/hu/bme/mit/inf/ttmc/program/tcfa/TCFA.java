package hu.bme.mit.inf.ttmc.program.tcfa;

import java.util.Collection;

public interface TCFA {
	
	public TCFALoc getInitLoc();
	public TCFALoc getFinalLoc();
	public TCFALoc getErrorLoc();
	
	public Collection<? extends TCFALoc> getLocs();
	public Collection<? extends TCFAEdge> getEdges();

}