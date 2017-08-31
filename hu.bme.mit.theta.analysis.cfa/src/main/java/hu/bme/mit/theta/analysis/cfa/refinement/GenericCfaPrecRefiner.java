package hu.bme.mit.theta.analysis.cfa.refinement;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.HashMap;
import java.util.Map;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.cfa.CfaPrec;
import hu.bme.mit.theta.analysis.cfa.CfaState;
import hu.bme.mit.theta.analysis.cfa.prec.GenericCfaPrec;
import hu.bme.mit.theta.analysis.expr.refinement.PrecRefiner;
import hu.bme.mit.theta.analysis.expr.refinement.Refutation;
import hu.bme.mit.theta.analysis.expr.refinement.RefutationToPrec;
import hu.bme.mit.theta.formalism.cfa.CFA.Loc;

public class GenericCfaPrecRefiner<S extends State, A extends Action, P extends Prec, R extends Refutation>
		implements PrecRefiner<CfaState<S>, A, CfaPrec<P>, R> {

	private final RefutationToPrec<P, R> refToPrec;

	private GenericCfaPrecRefiner(final RefutationToPrec<P, R> refToPrec) {
		this.refToPrec = checkNotNull(refToPrec);
	}

	public static <S extends State, A extends Action, P extends Prec, R extends Refutation> GenericCfaPrecRefiner<S, A, P, R> create(
			final RefutationToPrec<P, R> refToPrec) {
		return new GenericCfaPrecRefiner<>(refToPrec);
	}

	@Override
	public CfaPrec<P> refine(final CfaPrec<P> prec, final Trace<CfaState<S>, A> trace, final R refutation) {
		checkNotNull(trace);
		checkNotNull(prec);
		checkNotNull(refutation);
		checkArgument(prec instanceof GenericCfaPrec); // TODO: enforce this in a better way

		final GenericCfaPrec<P> genPrec = (GenericCfaPrec<P>) prec;
		final Map<Loc, P> runningPrecs = new HashMap<>();
		for (final CfaState<S> state : trace.getStates()) {
			runningPrecs.put(state.getLoc(), genPrec.getPrec(state.getLoc()));
		}

		for (int i = 0; i < trace.getStates().size(); ++i) {
			final Loc loc = trace.getState(i).getLoc();
			final P precForLoc = runningPrecs.get(loc);
			final P newPrecForLoc = refToPrec.toPrec(refutation, i);
			runningPrecs.put(loc, refToPrec.join(precForLoc, newPrecForLoc));
		}

		return genPrec.refine(runningPrecs);
	}

	@Override
	public String toString() {
		return getClass().getSimpleName();
	}
}
