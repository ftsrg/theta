package hu.bme.mit.theta.xsts.analysis;

import hu.bme.mit.theta.analysis.expr.ExprState;

import java.util.function.Predicate;

public class XstsStatePredicate<P extends Predicate, S extends ExprState> implements Predicate<XstsState<S>> {

	private final P pred;

	public XstsStatePredicate(final P pred) {
		this.pred = pred;
	}

	@Override
	public boolean test(XstsState<S> state) {
		return pred.test(state.getState());
	}
}
