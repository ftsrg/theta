package hu.bme.mit.theta.analysis.algorithm.cegar;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.common.waitlist.Waitlist;

public final class AbstractionState<S extends State, A extends Action, P extends Precision> {
	private final ARG<S, A> arg;
	private final Waitlist<ArgNode<S, A>> waitlist;
	private final P precision;

	private AbstractionState(final ARG<S, A> arg, final Waitlist<ArgNode<S, A>> waitlist, final P precision) {
		this.arg = checkNotNull(arg);
		this.waitlist = checkNotNull(waitlist);
		this.precision = checkNotNull(precision);
	}

	public static <S extends State, A extends Action, P extends Precision> AbstractionState<S, A, P> create(
			final ARG<S, A> arg, final Waitlist<ArgNode<S, A>> waitlist, final P precision) {
		return new AbstractionState<S, A, P>(arg, waitlist, precision);
	}

	////

	public ARG<S, A> getArg() {
		return arg;
	}

	public Waitlist<ArgNode<S, A>> getWaitlist() {
		return waitlist;
	}

	public P getPrecision() {
		return precision;
	}

}
