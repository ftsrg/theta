package hu.bme.mit.theta.analysis;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkElementIndex;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.List;

import com.google.common.collect.ImmutableList;

/**
 * Represents a trace of states and actions where each state is associated with
 * a precision.
 */
public final class PrecTrace<S extends State, A extends Action, P extends Precision> {
	private final List<P> precs;
	private final Trace<S, A> trace;

	private PrecTrace(final Trace<S, A> trace, final List<? extends P> precs) {
		this.precs = ImmutableList.copyOf(checkNotNull(precs));
		this.trace = checkNotNull(trace);
		checkArgument(precs.size() == trace.getStates().size());
	}

	public static <S extends State, A extends Action, P extends Precision> PrecTrace<S, A, P> of(
			final Trace<S, A> trace, final List<? extends P> precs) {
		return new PrecTrace<>(trace, precs);
	}

	public Trace<S, A> getTrace() {
		return trace;
	}

	public List<S> getStates() {
		return trace.getStates();
	}

	public List<A> getActions() {
		return trace.getActions();
	}

	public List<P> getPrecs() {
		return precs;
	}

	public S getState(final int i) {
		return trace.getState(i);
	}

	public A getAction(final int i) {
		return trace.getAction(i);
	}

	public P getPrec(final int i) {
		checkElementIndex(0, precs.size());
		return precs.get(i);
	}

}
