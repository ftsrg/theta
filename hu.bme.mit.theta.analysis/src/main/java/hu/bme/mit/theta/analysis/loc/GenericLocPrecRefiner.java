package hu.bme.mit.theta.analysis.loc;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

import java.util.List;
import java.util.stream.Collectors;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.PrecTrace;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.cegar.PrecRefiner;
import hu.bme.mit.theta.analysis.algorithm.cegar.PrecTraceRefiner;
import hu.bme.mit.theta.analysis.expr.Refutation;
import hu.bme.mit.theta.formalism.common.Edge;
import hu.bme.mit.theta.formalism.common.Loc;

public class GenericLocPrecRefiner<S extends State, A extends Action, P extends Prec, R extends Refutation, L extends Loc<L, E>, E extends Edge<L, E>>
		implements PrecRefiner<LocState<S, L, E>, A, LocPrec<P, L, E>, R> {

	PrecTraceRefiner<S, A, P, R> refiner;

	public GenericLocPrecRefiner(final PrecTraceRefiner<S, A, P, R> refiner) {
		this.refiner = checkNotNull(refiner);
	}

	@Override
	public LocPrec<P, L, E> refine(final Trace<LocState<S, L, E>, A> trace, final LocPrec<P, L, E> precision,
			final R refutation) {
		checkArgument(precision instanceof GenericLocPrecision); // TODO: enforce this in a better way
		final GenericLocPrecision<P, L, E> genPrecision = (GenericLocPrecision<P, L, E>) precision;
		final List<L> locs = trace.getStates().stream().map(LocState::getLoc).collect(Collectors.toList());
		final List<P> precs = locs.stream().map(l -> genPrecision.getPrecision(l)).collect(Collectors.toList());
		final List<S> states = trace.getStates().stream().map(LocState::getState).collect(Collectors.toList());
		final List<A> acts = trace.getActions();

		final PrecTrace<S, A, P> refinedPrecs = refiner.refine(PrecTrace.of(Trace.of(states, acts), precs), refutation);
		checkState(refinedPrecs.getPrecs().size() == locs.size());
		return genPrecision.refine(locs, refinedPrecs.getPrecs());
	}

}
