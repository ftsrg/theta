package hu.bme.mit.theta.analysis.prod;

import java.util.Collection;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;

@FunctionalInterface
public interface StrengtheningOperator<S1 extends State, S2 extends State, P1 extends Prec, P2 extends Prec> {

	public Collection<? extends Prod2State<S1, S2>> strengthen(final Collection<? extends Prod2State<S1, S2>> states,
			final Prod2Prec<P1, P2> prec);
}
