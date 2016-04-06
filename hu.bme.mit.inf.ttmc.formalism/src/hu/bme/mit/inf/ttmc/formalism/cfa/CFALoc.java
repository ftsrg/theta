package hu.bme.mit.inf.ttmc.formalism.cfa;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.formalism.common.Loc;

public interface CFALoc extends Loc {

	@Override
	public Collection<? extends CFAEdge> getInEdges();
	
	@Override
	public Collection<? extends CFAEdge> getOutEdges();

}
