package hu.bme.mit.theta.analysis.expr.refinement;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.common.ObjectUtils;

/**
 * A basic implementation of PrecRefiner that simply converts each element of
 * the Refutation into a Precision and joins them.
 */
public class JoiningPrecRefiner<S extends State, A extends Action, P extends Prec, R extends Refutation>
		implements PrecRefiner<S, A, P, R> {

	private final RefutationToPrec<P, R> refToPrec;

	private JoiningPrecRefiner(final RefutationToPrec<P, R> refToPrec) {
		this.refToPrec = checkNotNull(refToPrec);
	}

	public static <S extends State, A extends Action, P extends Prec, R extends Refutation> JoiningPrecRefiner<S, A, P, R> create(
			final RefutationToPrec<P, R> refToPrec) {
		return new JoiningPrecRefiner<>(refToPrec);
	}

	@Override
	public P refine(final P prec, final Trace<S, A> trace, final R refutation) {
		checkNotNull(trace);
		checkNotNull(prec);
		checkNotNull(refutation);

		P runningPrec = prec;
		for (int i = 0; i < trace.getStates().size(); ++i) {
			final P precFromRef = refToPrec.toPrec(refutation, i);
			runningPrec = refToPrec.join(runningPrec, precFromRef);
		}
		return runningPrec;
	}

	@Override
	public String toString() {
		return ObjectUtils.toStringBuilder(getClass().getSimpleName()).add(refToPrec).toString();
	}
}
