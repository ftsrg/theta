package hu.bme.mit.theta.analysis.loc;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.List;
import java.util.stream.Collectors;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.cegar.TraceRefiner;
import hu.bme.mit.theta.analysis.algorithm.cegar.TraceSeqRefiner;
import hu.bme.mit.theta.analysis.expr.Refutation;
import hu.bme.mit.theta.formalism.common.Edge;
import hu.bme.mit.theta.formalism.common.Loc;

public class LocTraceGenericRefiner<S extends State, A extends Action, P extends Precision, R extends Refutation, L extends Loc<L, E>, E extends Edge<L, E>>
		implements TraceRefiner<LocState<S, L, E>, A, LocPrecision<P, L, E>, R> {

	private final TraceSeqRefiner<LocState<S, L, E>, A, P, R> refiner;

	private LocTraceGenericRefiner(final TraceSeqRefiner<LocState<S, L, E>, A, P, R> refiner) {
		this.refiner = checkNotNull(refiner);
	}

	public static <S extends State, A extends Action, P extends Precision, R extends Refutation, L extends Loc<L, E>, E extends Edge<L, E>> LocTraceGenericRefiner<S, A, P, R, L, E> create(
			final TraceSeqRefiner<LocState<S, L, E>, A, P, R> refiner) {
		return new LocTraceGenericRefiner<>(refiner);
	}

	@Override
	public LocPrecision<P, L, E> refine(final Trace<LocState<S, L, E>, A> trace, final LocPrecision<P, L, E> precision,
			final R refutation) {
		checkArgument(precision instanceof GenericLocPrecision); // TODO: enforce this in a better way
		final GenericLocPrecision<P, L, E> genPrecision = (GenericLocPrecision<P, L, E>) precision;
		final List<L> locs = trace.getStates().stream().map(LocState::getLoc).collect(Collectors.toList());
		final List<P> precs = locs.stream().map(l -> genPrecision.getPrecision(l)).collect(Collectors.toList());
		final List<P> refinedPrecs = refiner.refine(trace, precs, refutation);
		return genPrecision.refine(locs, refinedPrecs);
	}

}
