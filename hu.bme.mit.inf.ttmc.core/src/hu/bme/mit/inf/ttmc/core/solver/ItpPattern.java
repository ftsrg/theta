package hu.bme.mit.inf.ttmc.core.solver;

import java.util.Collection;

public interface ItpPattern {
	
	public ItpMarker getMarker();
	public ItpPattern getParent();
	public Collection<ItpPattern> getChildren();
	
	public ItpPattern createChild(final ItpMarker marker);
	
}
