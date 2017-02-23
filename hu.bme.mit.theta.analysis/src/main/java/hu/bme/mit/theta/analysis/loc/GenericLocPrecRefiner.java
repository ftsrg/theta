package hu.bme.mit.theta.analysis.loc;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.cegar.PrecRefiner;
import hu.bme.mit.theta.analysis.expr.Refutation;
import hu.bme.mit.theta.analysis.expr.RefutationToPrec;
import hu.bme.mit.theta.formalism.common.Edge;
import hu.bme.mit.theta.formalism.common.Loc;

public class GenericLocPrecRefiner<S extends State, A extends Action, P extends Prec, R extends Refutation, L extends Loc<L, E>, E extends Edge<L, E>>
		implements PrecRefiner<LocState<S, L, E>, A, LocPrec<P, L, E>, R> {

	private final RefutationToPrec<P, R> refToPrec;

	private GenericLocPrecRefiner(final RefutationToPrec<P, R> refToPrec) {
		this.refToPrec = checkNotNull(refToPrec);
	}

	public static <S extends State, A extends Action, P extends Prec, R extends Refutation, L extends Loc<L, E>, E extends Edge<L, E>> GenericLocPrecRefiner<S, A, P, R, L, E> create(
			final RefutationToPrec<P, R> refToPrec) {
		return new GenericLocPrecRefiner<>(refToPrec);
	}

	@Override
	public LocPrec<P, L, E> refine(final Trace<LocState<S, L, E>, A> trace, final LocPrec<P, L, E> prec,
			final R refutation) {
		checkArgument(prec instanceof GenericLocPrec); // TODO: enforce this in a better way
		final GenericLocPrec<P, L, E> genPrec = (GenericLocPrec<P, L, E>) prec;

		throw new UnsupportedOperationException("Not implemented"); // TODO
	}

}
