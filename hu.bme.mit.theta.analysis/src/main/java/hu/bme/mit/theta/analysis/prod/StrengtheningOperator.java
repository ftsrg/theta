package hu.bme.mit.theta.analysis.prod;

import java.util.Collection;

import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;

@FunctionalInterface
public interface StrengtheningOperator<S1 extends State, S2 extends State, P1 extends Precision, P2 extends Precision> {

	public Collection<? extends Prod2State<S1, S2>> strengthen(final Collection<? extends Prod2State<S1, S2>> states,
			final Prod2Precision<P1, P2> precision);
}
