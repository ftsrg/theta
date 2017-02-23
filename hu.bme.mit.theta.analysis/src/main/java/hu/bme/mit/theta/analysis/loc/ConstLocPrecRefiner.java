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

public class ConstLocPrecRefiner<S extends State, A extends Action, P extends Prec, R extends Refutation, L extends Loc<L, E>, E extends Edge<L, E>>
		implements PrecRefiner<LocState<S, L, E>, A, LocPrec<P, L, E>, R> {

	private final RefutationToPrec<P, R> refToPrec;

	private ConstLocPrecRefiner(final RefutationToPrec<P, R> refToPrec) {
		this.refToPrec = checkNotNull(refToPrec);
	}

	public static <S extends State, A extends Action, P extends Prec, R extends Refutation, L extends Loc<L, E>, E extends Edge<L, E>> ConstLocPrecRefiner<S, A, P, R, L, E> create(
			final RefutationToPrec<P, R> refToPrec) {
		return new ConstLocPrecRefiner<>(refToPrec);
	}

	@Override
	public LocPrec<P, L, E> refine(final Trace<LocState<S, L, E>, A> trace, final LocPrec<P, L, E> prec,
			final R refutation) {
		checkNotNull(trace);
		checkNotNull(prec);
		checkNotNull(refutation);
		checkArgument(prec instanceof ConstLocPrec); // TODO: enforce this in a better way

		final ConstLocPrec<P, L, E> constPrec = (ConstLocPrec<P, L, E>) prec;
		P runningPrec = constPrec.getPrec();
		for (int i = 0; i < trace.getStates().size(); ++i) {
			final P precFromRef = refToPrec.toPrec(refutation, i);
			runningPrec = refToPrec.join(runningPrec, precFromRef);
		}
		return constPrec.refine(runningPrec);
	}

	@Override
	public String toString() {
		return getClass().getSimpleName();
	}

}
