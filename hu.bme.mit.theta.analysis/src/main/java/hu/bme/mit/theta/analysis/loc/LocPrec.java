package hu.bme.mit.theta.analysis.loc;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.formalism.common.Edge;
import hu.bme.mit.theta.formalism.common.Loc;

public interface LocPrec<P extends Prec, L extends Loc<L, E>, E extends Edge<L, E>> extends Prec {

	P getPrec(final L loc);
}
