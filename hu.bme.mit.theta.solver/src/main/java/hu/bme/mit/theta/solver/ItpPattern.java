package hu.bme.mit.theta.solver;

import java.util.Collection;

public interface ItpPattern {

	ItpMarker getMarker();

	ItpPattern getParent();

	Collection<ItpPattern> getChildren();

	ItpPattern createChild(final ItpMarker marker);

}
