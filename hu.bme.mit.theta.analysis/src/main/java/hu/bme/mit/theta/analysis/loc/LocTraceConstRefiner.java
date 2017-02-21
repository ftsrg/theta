package hu.bme.mit.theta.analysis.loc;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.cegar.TraceRefiner;
import hu.bme.mit.theta.analysis.expr.Refutation;
import hu.bme.mit.theta.formalism.common.Edge;
import hu.bme.mit.theta.formalism.common.Loc;

public class LocTraceConstRefiner<S extends State, A extends Action, P extends Precision, R extends Refutation, L extends Loc<L, E>, E extends Edge<L, E>>
		implements TraceRefiner<LocState<S, L, E>, A, LocPrecision<P, L, E>, R> {

	private final TraceRefiner<LocState<S, L, E>, A, P, R> refiner;

	private LocTraceConstRefiner(final TraceRefiner<LocState<S, L, E>, A, P, R> refiner) {
		this.refiner = checkNotNull(refiner);
	}

	public static <S extends State, A extends Action, P extends Precision, R extends Refutation, L extends Loc<L, E>, E extends Edge<L, E>> LocTraceConstRefiner<S, A, P, R, L, E> create(
			final TraceRefiner<LocState<S, L, E>, A, P, R> refiner) {
		return new LocTraceConstRefiner<>(refiner);
	}

	@Override
	public LocPrecision<P, L, E> refine(final Trace<LocState<S, L, E>, A> trace, final LocPrecision<P, L, E> precision,
			final R refutation) {
		checkArgument(precision instanceof ConstLocPrecision); // TODO: enforce this in a better way
		final ConstLocPrecision<P, L, E> constPrecision = (ConstLocPrecision<P, L, E>) precision;
		final P innerPrec = constPrecision.getPrecision();
		final P refinedInnerPrec = refiner.refine(trace, innerPrec, refutation);
		return constPrecision.refine(refinedInnerPrec);
	}

}
