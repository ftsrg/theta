package hu.bme.mit.theta.analysis.loc;

import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.formalism.common.Edge;
import hu.bme.mit.theta.formalism.common.Loc;

public interface LocPrecision<P extends Precision, L extends Loc<L, E>, E extends Edge<L, E>> extends Precision {

	P getPrecision(final L loc);
}
