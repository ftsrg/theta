package hu.bme.mit.theta.analysis.loc;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.cegar.PrecRefiner;
import hu.bme.mit.theta.analysis.expr.Refutation;
import hu.bme.mit.theta.formalism.common.Edge;
import hu.bme.mit.theta.formalism.common.Loc;

public class ConstLocPrecRefiner<S extends State, A extends Action, P extends Prec, R extends Refutation, L extends Loc<L, E>, E extends Edge<L, E>>
		implements PrecRefiner<LocState<S, L, E>, A, LocPrec<P, L, E>, R> {

	private final PrecRefiner<LocState<S, L, E>, A, P, R> refiner;

	private ConstLocPrecRefiner(final PrecRefiner<LocState<S, L, E>, A, P, R> refiner) {
		this.refiner = checkNotNull(refiner);
	}

	public static <S extends State, A extends Action, P extends Prec, R extends Refutation, L extends Loc<L, E>, E extends Edge<L, E>> ConstLocPrecRefiner<S, A, P, R, L, E> create(
			final PrecRefiner<LocState<S, L, E>, A, P, R> refiner) {
		return new ConstLocPrecRefiner<>(refiner);
	}

	@Override
	public LocPrec<P, L, E> refine(final Trace<LocState<S, L, E>, A> trace, final LocPrec<P, L, E> precision,
			final R refutation) {
		checkArgument(precision instanceof ConstLocPrec); // TODO: enforce this in a better way
		final ConstLocPrec<P, L, E> constPrecision = (ConstLocPrec<P, L, E>) precision;
		final P innerPrec = constPrecision.getPrecision();
		final P refinedInnerPrec = refiner.refine(trace, innerPrec, refutation);
		return constPrecision.refine(refinedInnerPrec);
	}

}
