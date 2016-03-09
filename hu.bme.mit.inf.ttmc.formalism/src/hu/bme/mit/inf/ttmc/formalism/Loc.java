package hu.bme.mit.inf.ttmc.formalism;

import java.util.Collection;

public interface Loc {
	
	public Collection<? extends Edge> getInEdges();
	
	public Collection<? extends Edge> getOutEdges();
	
}
