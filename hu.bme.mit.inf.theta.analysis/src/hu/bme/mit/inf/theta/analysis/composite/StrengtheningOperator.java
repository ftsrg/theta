package hu.bme.mit.inf.theta.analysis.composite;

import java.util.Collection;

import hu.bme.mit.inf.theta.analysis.Precision;
import hu.bme.mit.inf.theta.analysis.State;

@FunctionalInterface
public interface StrengtheningOperator<S1 extends State, S2 extends State, P1 extends Precision, P2 extends Precision> {

	public Collection<? extends CompositeState<S1, S2>> strengthen(
			final Collection<? extends CompositeState<S1, S2>> states, final CompositePrecision<P1, P2> precision);

}
