package hu.bme.mit.theta.analysis.loc;

import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.formalism.common.Edge;
import hu.bme.mit.theta.formalism.common.Loc;

public final class GenericLocPrecision<P extends Precision, L extends Loc<L, E>, E extends Edge<L, E>>
		implements LocPrecision<P, L, E> {

	@Override
	public P getPrecision(final L loc) {
		// TODO Auto-generated method stub
		return null;
	}

}
