package hu.bme.mit.theta.analysis.loc;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.cegar.Refiner;
import hu.bme.mit.theta.analysis.algorithm.cegar.RefinerResult;
import hu.bme.mit.theta.formalism.common.Edge;
import hu.bme.mit.theta.formalism.common.Loc;

public final class LocRefiner<S extends State, A extends Action, P extends Precision, L extends Loc<L, E>, E extends Edge<L, E>>
		implements Refiner<LocState<S, L, E>, A, LocPrecision<P, L, E>> {

	private final Refiner<LocState<S, L, E>, A, P> refiner;

	private LocRefiner(final Refiner<LocState<S, L, E>, A, P> refiner) {
		this.refiner = refiner;
	}

	public static <S extends State, A extends Action, P extends Precision, L extends Loc<L, E>, E extends Edge<L, E>> LocRefiner<S, A, P, L, E> create(
			final Refiner<LocState<S, L, E>, A, P> refiner) {
		return new LocRefiner<>(refiner);
	}

	@Override
	public RefinerResult<LocState<S, L, E>, A, LocPrecision<P, L, E>> refine(final ARG<LocState<S, L, E>, A> arg,
			final LocPrecision<P, L, E> precision) {
		// TODO: we assume that the precision is the same for each location,
		// therefore we only fetch the precision of the first initial location
		final RefinerResult<LocState<S, L, E>, A, P> refinerResult = refiner.refine(arg,
				precision.getPrecision(arg.getInitNodes().findFirst().get().getState().getLoc()));
		if (refinerResult.isUnsafe()) {
			return RefinerResult.unsafe(refinerResult.asUnsafe().getCex());
		} else {
			return RefinerResult.spurious(LocPrecision.constant(refinerResult.asSpurious().getRefinedPrecision()));
		}
	}

}
