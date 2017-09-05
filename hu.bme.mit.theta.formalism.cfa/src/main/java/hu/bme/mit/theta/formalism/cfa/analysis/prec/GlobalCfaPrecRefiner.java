package hu.bme.mit.theta.formalism.cfa.analysis.prec;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.refinement.PrecRefiner;
import hu.bme.mit.theta.analysis.expr.refinement.Refutation;
import hu.bme.mit.theta.analysis.expr.refinement.RefutationToPrec;
import hu.bme.mit.theta.formalism.cfa.analysis.CfaPrec;
import hu.bme.mit.theta.formalism.cfa.analysis.CfaState;

public class GlobalCfaPrecRefiner<S extends ExprState, A extends Action, P extends Prec, R extends Refutation>
		implements PrecRefiner<CfaState<S>, A, CfaPrec<P>, R> {

	private final RefutationToPrec<P, R> refToPrec;

	private GlobalCfaPrecRefiner(final RefutationToPrec<P, R> refToPrec) {
		this.refToPrec = checkNotNull(refToPrec);
	}

	public static <S extends ExprState, A extends Action, P extends Prec, R extends Refutation> GlobalCfaPrecRefiner<S, A, P, R> create(
			final RefutationToPrec<P, R> refToPrec) {
		return new GlobalCfaPrecRefiner<>(refToPrec);
	}

	@Override
	public CfaPrec<P> refine(final CfaPrec<P> prec, final Trace<CfaState<S>, A> trace, final R refutation) {
		checkNotNull(trace);
		checkNotNull(prec);
		checkNotNull(refutation);
		checkArgument(prec instanceof GlobalCfaPrec); // TODO: enforce this in a better way

		final GlobalCfaPrec<P> constPrec = (GlobalCfaPrec<P>) prec;
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
