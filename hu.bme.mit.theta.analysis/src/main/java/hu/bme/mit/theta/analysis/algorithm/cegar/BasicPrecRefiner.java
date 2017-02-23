package hu.bme.mit.theta.analysis.algorithm.cegar;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expr.Refutation;
import hu.bme.mit.theta.analysis.expr.RefutationToPrec;

public class BasicPrecRefiner<S extends State, A extends Action, P extends Prec, R extends Refutation>
		implements PrecRefiner<S, A, P, R> {

	private final RefutationToPrec<P, R> refToPrec;

	private BasicPrecRefiner(final RefutationToPrec<P, R> refToPrec) {
		this.refToPrec = refToPrec;
	}

	public static <S extends State, A extends Action, P extends Prec, R extends Refutation> BasicPrecRefiner<S, A, P, R> create(
			final RefutationToPrec<P, R> refToPrec) {
		return new BasicPrecRefiner<>(refToPrec);
	}

	@Override
	public P refine(final Trace<S, A> trace, final P prec, final R refutation) {
		P runningPrec = prec;
		for (int i = 0; i < trace.getStates().size(); ++i) {
			final P precFromRef = refToPrec.toPrec(refutation, i);
			runningPrec = refToPrec.join(runningPrec, precFromRef);
		}
		return runningPrec;
	}
}
